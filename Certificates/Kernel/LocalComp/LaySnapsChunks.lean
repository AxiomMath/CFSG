module

public meta import Lean
public meta import Certificates.Kernel.LocalQT.Cmd
public import Certificates.Data.Kernel.OpsRenL
public import Certificates.Kernel.LocalQT.Cmd

open Lean Elab Command Meta CFSG.KC.LQT.Cmd

public section

namespace CFSG.KC.LaySnapsChunks

meta def natOfE (e : Expr) : CoreM Nat := do
  match e.consumeMData with
  | .lit (.natVal x) => return x
  | e => throwError "#lay_snaps_chunks: not a Nat literal: {e}"

meta partial def listOfE (e : Expr) : CoreM (List Expr) := do
  let e := e.consumeMData
  if e.isAppOfArity ``List.cons 3 then
    return e.appFn!.appArg! :: (← listOfE e.appArg!)
  else if e.isAppOfArity ``List.nil 1 then
    return []
  else
    throwError "#lay_snaps_chunks: not a list literal: {e}"

meta def pairOfE (e : Expr) : CoreM (Expr × Expr) := do
  let e := e.consumeMData
  if e.isAppOfArity ``Prod.mk 4 then
    return (e.appFn!.appArg!, e.appArg!)
  else
    throwError "#lay_snaps_chunks: not a pair literal: {e}"

meta def valueOf (n : Name) : CoreM Expr := do
  let some (.defnInfo v) := (← getEnv).find? n | throwError "{n} is not a definition"
  return v.value

meta def runChunk (c : LayV) (S : List Nat) (n : Nat) (ops : List (List Nat)) (out : List Nat) :
    CoreM (List Nat) := do
  let mut R : Array Nat := (S ++ List.replicate (n - S.length) c.ONE).toArray
  for o in ops do
    match o with
    | [0, i, j, k] => R := R.set! k (c.mul (R.getD i c.ONE) (R.getD j c.ONE))
    | [e, i, _, k] => R := R.set! k (c.pow (R.getD i c.ONE) e)
    | _ => throwError "#lay_snaps_chunks: not an operation: {o}"
  return out.map fun r => R.getD r c.ONE

elab "#lay_snaps_chunks " pre:ident p:num d:num a:ident b:ident cs:ident : command => do
  let pre := pre.getId
  let A ← liftCoreM <| do natOfE (← valueOf (← realizeGlobalConstNoOverload a))
  let B ← liftCoreM <| do natOfE (← valueOf (← realizeGlobalConstNoOverload b))
  let chs ← liftCoreM <| do listOfE (← valueOf (← realizeGlobalConstNoOverload cs))
  let c := layOf p.getNat d.getNat
  withSync do
    let listT := mkApp (mkConst ``List [0]) natE
    let mut S : List Nat := [A, B]
    addDef (pre ++ `S0) listT (natList S)
    let mut i := 0
    for ch in chs do
      let (nE, rest) ← pairOfE ch
      let (opsE, outE) ← pairOfE rest
      let ops ← (← listOfE opsE).mapM fun o => do (← listOfE o).mapM natOfE
      S ← runChunk c S (← natOfE nE) ops (← (← listOfE outE).mapM natOfE)
      i := i + 1
      addDef (pre ++ Name.mkSimple s!"S{i}") listT (natList S)
    let sl := (List.range (i + 1)).foldr
      (fun k acc => mkApp3 (mkConst ``List.cons [0]) listT
        (mkConst (pre ++ Name.mkSimple s!"S{k}")) acc)
      (mkApp (mkConst ``List.nil [0]) listT)
    addDef (pre ++ `SL) (mkApp (mkConst ``List [0]) listT) sl

end CFSG.KC.LaySnapsChunks

end
