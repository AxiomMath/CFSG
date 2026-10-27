module

public meta import Lean
public meta import Certificates.Kernel.LocalQT.Cmd
public import Certificates.Data.Kernel.LocalQT.Sec
public import Certificates.Kernel.LocalQT.Cmd

open Lean Elab Command Meta CFSG.KC.LQT.Cmd CFSG.SectionRank.Native

public section

namespace CFSG.KC.LaySnaps

meta def natOf (n : Name) : CoreM Nat := do
  let some (.defnInfo v) := (← getEnv).find? n | throwError "{n} is not a definition"
  match v.value.consumeMData with
  | .lit (.natVal x) => return x
  | e => throwError "{n} is not a Nat literal: {e}"

meta def runOps (c : LayV) (R : Array Nat) (ops : List Op) : Array Nat :=
  ops.foldl (fun R o => match o with
    | .mul i j t => R.set! t (c.mul R[i]! R[j]!)
    | .pow e i t => R.set! t (c.pow R[i]! e)) R

meta unsafe def evalProg (n : Name) : CoreM (List Op) := evalConst (List Op) n

elab "#lay_snaps " pre:ident p:num d:num a:ident b:ident prog:ident n:num k:num : command => do
  let pre := pre.getId
  let A ← liftCoreM <| natOf (← liftCoreM <| realizeGlobalConstNoOverload a)
  let B ← liftCoreM <| natOf (← liftCoreM <| realizeGlobalConstNoOverload b)
  let ops ← liftCoreM <| unsafe evalProg (← liftCoreM <| realizeGlobalConstNoOverload prog)
  let c := layOf p.getNat d.getNat
  let n := n.getNat
  let k := k.getNat
  let m := (ops.length + k - 1) / k
  withSync do
    let mut R : Array Nat :=
      (Array.range n).map fun r => if r == 0 then A else if r == 1 then B else c.ONE
    let listT := mkApp (mkConst ``List [0]) natE
    addDef (pre ++ `S0) listT (natList R.toList)
    for i in [0:m] do
      R := runOps c R ((ops.drop (i * k)).take k)
      addDef (pre ++ Name.mkSimple s!"S{i + 1}") listT (natList R.toList)
    let sl := (List.range (m + 1)).foldr
      (fun i acc => mkApp3 (mkConst ``List.cons [0]) listT
        (mkConst (pre ++ Name.mkSimple s!"S{i}")) acc)
      (mkApp (mkConst ``List.nil [0]) listT)
    addDef (pre ++ `SL) (mkApp (mkConst ``List [0]) listT) sl
    addDef (pre ++ `m) natE (lit m)

end CFSG.KC.LaySnaps

end
