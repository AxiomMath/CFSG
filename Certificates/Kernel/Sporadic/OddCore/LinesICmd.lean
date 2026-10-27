module

public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import Certificates.Data.Kernel.Spor.DecLinesI
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.Tab

open Lean Elab Command

public section

open CFSG.KC.Tab in
elab "#ks_linesI " pre:ident aId:ident : command => do
  let P := pre.getId
  let aN ← liftCoreM <| realizeGlobalConstNoOverload aId
  let a ← liftTermElabM <| unsafe evalConst (Array (List Int)) aN
  let intT := mkConst ``Int
  let lnT := mkApp (mkConst ``List [0]) intT
  let mkL (ty : Expr) (xs : List Expr) : Expr :=
    xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) ty x acc) (mkApp (mkConst ``List.nil [0]) ty)
  let intE (z : Int) : Expr := match z with
    | .ofNat n => mkApp (mkConst ``Int.ofNat) (lit n)
    | .negSucc n => mkApp (mkConst ``Int.negSucc) (lit n)
  let e := mkL lnT (a.toList.map fun r => mkL intT (r.map intE))
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `E) (mkApp (mkConst ``List [0]) lnT) e
    let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkApp2 (mkConst ``CFSG.KS.DecLines.linesChkI) (mkConst (P ++ `chars))
        (mkApp (mkConst ``CFSG.KS.DecLines.encodeLI) (mkConst (P ++ `E))))
      (mkConst ``Bool.true)
    CFSG.KC.addThmDecl <| { name := P ++ `ok, levelParams := [], type := ty, value := reflBoolTrue }

end
