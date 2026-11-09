module

public meta import Lean
public meta import Certificates.Kernel.LocalQT.Cmd
public meta import Certificates.Kernel.LocalComp.LaySnapsChunks
public import Certificates.Data.Kernel.LyDce.CoverWalkCut
public import Certificates.Kernel.LocalQT.Cmd

open Lean Elab Command Meta CFSG.KC.LQT.Cmd CFSG.KC.LaySnapsChunks

public section

namespace CFSG.KC.LyDce.Cmd

meta def W : Nat := 131072

meta def dswM (s m x : Nat) : Nat :=
  let t := ((x >>> s) ^^^ x) &&& m
  x ^^^ (t ^^^ (t <<< s))

meta def stageShiftM (k i : Nat) : Nat := if i < k then 1 <<< (k - 1 - i) else 1 <<< (i + 1 - k)

meta def net2M (N X : Nat) : Nat := Id.run do
  let U := 1 + (1 <<< W)
  let ones := (1 <<< W) - 1
  let mut x := X
  for i in [0:33] do
    x := dswM (stageShiftM 17 i) (((N >>> (i * W)) &&& ones) * U) x
  return x

meta def triM (Nc Nd X : Nat) : Nat × Nat × Nat := (X, net2M Nc X, net2M Nd X)

meta def tripleOfE (e : Expr) : CoreM (Nat × Nat × Nat) := do
  let (a, r) ← pairOfE e
  let (b, c) ← pairOfE r
  return (← natOfE a, ← natOfE b, ← natOfE c)

elab "#lydce_cuts " pre:ident nc:ident nd:ident o0:ident dfs:ident i:num
    "[" cuts:num,* "]" : command => do
  let pre := pre.getId
  let Nc ← liftCoreM do natOfE (← valueOf (← realizeGlobalConstNoOverload nc))
  let Nd ← liftCoreM do natOfE (← valueOf (← realizeGlobalConstNoOverload nd))
  let O ← liftCoreM do (← listOfE (← valueOf (← realizeGlobalConstNoOverload o0))).mapM natOfE
  let ws ← liftCoreM do listOfE (← valueOf (← realizeGlobalConstNoOverload dfs))
  let some wE := ws[i.getNat]? | throwError "#lydce_cuts: no walk {i.getNat}"
  let es ← liftCoreM do (← listOfE wE).mapM tripleOfE
  let M₀ := O.foldl (fun x a => x ||| (1 <<< a)) 0
  let salt0 := (3 ^ 82713) % (1 <<< W)
  let X₀ := (M₀ <<< W) ||| salt0
  let cuts := cuts.getElems.toList.map (·.getNat)
  withSync do
    let mut st : List (Nat × Nat × Nat) := [triM Nc Nd X₀]
    let mut done := 0
    let mut j := 1
    for a in cuts do
      if a < done then throwError "#lydce_cuts: cuts must increase"
      for e in (es.drop done).take (a - done) do
        match st.drop e.2.1 with
        | [] => throwError "#lydce_cuts: empty stack"
        | top :: rest =>
          let X := if e.2.2 == 0 then top.2.1 else if e.2.2 == 1 then top.2.2 else top.1
          let rest' := if e.2.2 == 2 then rest else top :: rest
          st := triM Nc Nd X :: rest'
      done := a
      addDef (pre ++ Name.mkSimple s!"X{j}") (mkApp (mkConst ``List [0]) natE)
        (natList (st.map (·.1)))
      j := j + 1

end CFSG.KC.LyDce.Cmd

end
