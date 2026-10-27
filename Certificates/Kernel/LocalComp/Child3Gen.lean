module

public import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean

open Lean Elab Command

public section

namespace CFSG.KC.Child3Gen

open CFSG.KC.Tab CFSG.KS.RawGen

meta def comp (t u : Array Nat) : Array Nat := u.map fun x => t[x]!

meta def inv (t : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate t.size 0
  for i in [0:t.size] do
    r := r.set! t[i]! i
  return r

meta def listE (l : List Nat) : Expr :=
  l.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) natT (lit x) acc)
    (mkApp (mkConst ``List.nil [0]) natT)

elab "#lc_forest " pre:ident nn:num sId:ident " [" rs:num,* "]" : command => do
  let P := pre.getId
  let n := nn.getNat
  let S ← liftTermElabM <| unsafe evalConst (Array (Array Nat))
    (← liftCoreM <| realizeGlobalConstNoOverload sId)
  let roots : List Nat := rs.getElems.toList.map (·.getNat)
  let mut par := Array.replicate n 0
  let mut lab := Array.replicate n 0
  let mut dep := Array.replicate n (n + 1)
  let mut queue : Array Nat := #[]
  for r in roots do
    dep := dep.set! r 0
    queue := queue.push r
  let mut h := 0
  while h < queue.size do
    let x := queue[h]!
    h := h + 1
    for l in [0:S.size] do
      let y := S[l]![x]!
      if y < n && dep[y]! == n + 1 then
        dep := dep.set! y (dep[x]! + 1)
        par := par.set! y x
        lab := lab.set! y l
        queue := queue.push y
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `FP) par
    addTree (P ++ `FL) lab
    addTree (P ++ `FD) dep

elab "#lc_reps " pre:ident ww:num gId:ident rId:ident : command => do
  let P := pre.getId
  let w := ww.getNat
  let G ← liftTermElabM <| unsafe evalConst (Array (Array Nat))
    (← liftCoreM <| realizeGlobalConstNoOverload gId)
  let reps ← liftTermElabM <| unsafe evalConst (List (Array Nat))
    (← liftCoreM <| realizeGlobalConstNoOverload rId)
  let g := G.size
  let GI := G.map inv
  let mut E : Array (Array Nat) := #[]
  let mut Pa : Array Nat := #[]
  let mut La : Array Nat := #[]
  let mut CI : Array Nat := #[]
  let mut CS : Array Nat := #[]
  let mut OFF : Array Nat := #[]
  let mut Ka : Array Nat := #[]
  for i in [0:reps.length] do
    let o := E.size
    OFF := OFF.push o
    let mut cls : Array (Array Nat) := #[reps[i]!]
    let mut idx : Std.HashMap (Array Nat) Nat := ({} : Std.HashMap (Array Nat) Nat).insert reps[i]! 0
    let mut par : Array Nat := #[0]
    let mut lab : Array Nat := #[0]
    let mut q := 0
    while q < cls.size do
      let y := cls[q]!
      q := q + 1
      for l in [0:g] do
        let z := comp (comp G[l]! y) GI[l]!
        if !idx.contains z then
          idx := idx.insert z cls.size
          cls := cls.push z
          par := par.push (q - 1)
          lab := lab.push l
    for k in [0:cls.size] do
      E := E.push cls[k]!
      Pa := Pa.push par[k]!
      La := La.push lab[k]!
      CI := CI.push i
      for l in [0:g] do
        let z := comp (comp G[l]! cls[k]!) GI[l]!
        Ka := Ka.push (idx.getD z cls.size)
    CS := CS.push cls.size
  let Ep := E.map (pack w)
  let S := (Array.range Ep.size).qsort fun a b => Ep[a]! < Ep[b]!
  let mut SI := Array.replicate Ep.size 0
  for m in [0:S.size] do
    SI := SI.set! S[m]! m
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `CS) (mkApp (mkConst ``List [0]) natT) (listE CS.toList)
    addDef (P ++ `OFF) (mkApp (mkConst ``List [0]) natT) (listE OFF.toList)
    addTree (P ++ `CI) CI
    addTree (P ++ `E) Ep
    addTree (P ++ `P) Pa
    addTree (P ++ `L) La
    addTree (P ++ `K) Ka
    addTree (P ++ `S) S
    addTree (P ++ `SI) SI
    addTree (P ++ `GP) (G.map (pack w))
    addTree (P ++ `GIP) (GI.map (pack w))
    addDef (P ++ `N) natT (lit Ep.size)

end CFSG.KC.Child3Gen

end
