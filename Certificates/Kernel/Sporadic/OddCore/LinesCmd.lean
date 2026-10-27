module

public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import Certificates.Data.Kernel.Spor.DecLines
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.Tab

open Lean Elab Command

public section

open CFSG.KC.Tab in
elab "#ks_lines " pre:ident aId:ident : command => do
  let P := pre.getId
  let aN ← liftCoreM <| realizeGlobalConstNoOverload aId
  let a ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) aN
  let lnT := mkApp (mkConst ``List [0]) natT
  let mkL (ty : Expr) (xs : List Expr) : Expr :=
    xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) ty x acc) (mkApp (mkConst ``List.nil [0]) ty)
  let e := mkL lnT (a.toList.map fun r => mkL natT (r.toList.map lit))
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `E) (mkApp (mkConst ``List [0]) lnT) e
    let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkApp2 (mkConst ``CFSG.KS.DecLines.linesChk) (mkConst (P ++ `chars))
        (mkApp (mkConst ``CFSG.KS.DecLines.encodeL) (mkConst (P ++ `E))))
      (mkConst ``Bool.true)
    CFSG.KC.addThmDecl <| { name := P ++ `ok, levelParams := [], type := ty, value := reflBoolTrue }

end
