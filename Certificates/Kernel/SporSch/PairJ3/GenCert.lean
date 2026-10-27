module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Tab
public import Init
public import CFSG.Certificates.Kernel.Common.Tab

open Lean Elab Command

public section

open CFSG.KC.Tab in
elab "#kss_pomdata " pre:ident cId:ident : command => do
  let P := pre.getId
  let cN ← liftCoreM <| realizeGlobalConstNoOverload cId
  let R ← liftTermElabM <| unsafe evalConst
    (List (List Nat) × List (Nat × List (Nat × Nat × Nat))) cN
  let natE := natT
  let lstT := fun (t : Expr) => mkApp (mkConst ``List [0]) t
  let mkL := fun (t : Expr) (xs : List Expr) =>
    xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) t x acc) (mkApp (mkConst ``List.nil [0]) t)
  let pairT := fun (a b : Expr) => mkApp2 (mkConst ``Prod [0, 0]) a b
  let mkP := fun (a b : Expr) (x y : Expr) => mkApp4 (mkConst ``Prod.mk [0, 0]) a b x y
  let triT := pairT natE (pairT natE natE)
  let orbE := mkL (lstT natE) (R.1.map fun o => mkL natE (o.map lit))
  let mT := pairT natE (lstT triT)
  let msE := mkL mT (R.2.map fun m => mkP natE (lstT triT) (lit m.1)
    (mkL triT (m.2.map fun t => mkP natE (pairT natE natE) (lit t.1) (mkP natE natE (lit t.2.1) (lit t.2.2)))))
  let ty := pairT (lstT (lstT natE)) (lstT mT)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `R) ty (mkP (lstT (lstT natE)) (lstT mT) orbE msE)

end
