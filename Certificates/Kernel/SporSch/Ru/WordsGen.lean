module

public import Certificates.Kernel.Sporadic.RawGen
public meta import Lean

open Lean Elab Command

public section

open CFSG.KC.Tab in
elab "#kss_words " pre:ident cId:ident : command => do
  let cN ← liftCoreM <| realizeGlobalConstNoOverload cId
  let W ← liftTermElabM <| unsafe evalConst (List (List (Nat × Bool))) cN
  let natE := mkConst ``Nat
  let boolE := mkConst ``Bool
  let pairT := mkApp2 (mkConst ``Prod [0, 0]) natE boolE
  let wordT := mkApp (mkConst ``List [0]) pairT
  let mkPair := fun (l : Nat × Bool) => mkAppN (mkConst ``Prod.mk [0, 0])
    #[natE, boolE, mkRawNatLit l.1, mkConst (if l.2 then ``Bool.true else ``Bool.false)]
  let mkList := fun (ty : Expr) (xs : List Expr) => xs.foldr
    (fun x acc => mkApp3 (mkConst ``List.cons [0]) ty x acc) (mkApp (mkConst ``List.nil [0]) ty)
  let e := mkList wordT (W.map fun v => mkList pairT (v.map mkPair))
  liftCoreM <| addDef pre.getId (mkApp (mkConst ``List [0]) wordT) e

end
