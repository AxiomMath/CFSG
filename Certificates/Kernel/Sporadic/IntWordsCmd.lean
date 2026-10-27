module

public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
public import CFSG.Certificates.Kernel.Common.Tab

open Lean Elab Command

public section

open CFSG.KC.Tab in
elab "#kc_intwords " pre:ident sId:ident : command => do
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let a ← liftTermElabM <| unsafe evalConst (Array (List Int)) sN
  let intT := mkConst ``Int
  let lnT := mkApp (mkConst ``List [0]) intT
  let mkL (ty : Expr) (xs : List Expr) : Expr :=
    xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) ty x acc)
      (mkApp (mkConst ``List.nil [0]) ty)
  let intE (z : Int) : Expr := match z with
    | .ofNat n => mkApp (mkConst ``Int.ofNat) (lit n)
    | .negSucc n => mkApp (mkConst ``Int.negSucc) (lit n)
  let e := mkL lnT (a.toList.map fun r => mkL intT (r.map intE))
  withSync <| addDef pre.getId (mkApp (mkConst ``List [0]) lnT) e

end
