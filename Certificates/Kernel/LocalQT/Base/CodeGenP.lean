module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Common.Tab

open Lean Elab Command

public section

open CFSG.KC.Tab in
elab "#kqt_pairs " pre:ident x:ident eId:ident : command => do
  let eN ← liftCoreM <| realizeGlobalConstNoOverload eId
  let l ← liftTermElabM <| unsafe evalConst (List (Nat × Nat)) eN
  let pT := mkApp2 (mkConst ``Prod [0, 0]) natT natT
  let e := l.foldr (fun p acc => mkApp3 (mkConst ``List.cons [0]) pT
    (mkApp4 (mkConst ``Prod.mk [0, 0]) natT natT (lit p.1) (lit p.2)) acc)
    (mkApp (mkConst ``List.nil [0]) pT)
  withSync <| addDef (pre.getId ++ x.getId) (mkApp (mkConst ``List [0]) pT) e

end
