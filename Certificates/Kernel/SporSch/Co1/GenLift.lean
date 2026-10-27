module

public meta import Lean
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public import Certificates.Kernel.Sporadic.RawGen

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kss_co1lift " pre:ident rId:ident zId:ident : command => do
  let rN ← liftCoreM <| realizeGlobalConstNoOverload rId
  let zN ← liftCoreM <| realizeGlobalConstNoOverload zId
  let R ← liftTermElabM <| unsafe evalConst (Array Nat) rN
  let z ← liftTermElabM <| unsafe evalConst Nat zN
  let P := pre.getId
  let val := fun (m : Nat) => if m < 2300 then R[m]! else z ^^^ R[m - 2300]!
  let Ms := ((List.range 4600).toArray.qsort fun a b => val a < val b).toList
  let natE := mkConst ``Nat
  let lst := Ms.foldr (fun m acc => mkApp3 (mkConst ``List.cons [0]) natE (lit m) acc)
    (mkApp (mkConst ``List.nil [0]) natE)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `PR) natT (lit (pack 24 R))
    addDef (P ++ `Ms) (mkApp (mkConst ``List [0]) natE) lst

end
