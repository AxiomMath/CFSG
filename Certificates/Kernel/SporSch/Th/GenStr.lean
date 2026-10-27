module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.Tab
public import Lean.Exception

open Lean Elab Command

public section

open CFSG.KC.Tab in
elab "#kss_strof " pre:ident cId:ident : command => do
  let P := pre.getId
  let cN ← liftCoreM <| realizeGlobalConstNoOverload cId
  let env ← getEnv
  let some ci := env.find? cN | throwError "unknown constant"
  let some val := ci.value? | throwError "no value"
  let some s := (val.find? fun e => e.isStringLit).bind fun e =>
      match e with | .lit (.strVal s) => some s | _ => none
    | throwError "no string literal"
  let charE : Expr := mkConst ``Char
  let mk (ch : Char) : Expr := mkApp (mkConst ``Char.ofNat) (mkRawNatLit ch.toNat)
  let lst := s.toList.foldr (fun ch acc => mkApp3 (mkConst ``List.cons [0]) charE (mk ch) acc)
    (mkApp (mkConst ``List.nil [0]) charE)
  let lty := mkApp (mkConst ``List [0]) charE
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `chars) lty lst
    let ofL := mkApp (mkConst ``String.ofList) (mkConst (P ++ `chars))
    let val' := val.replace fun e => if e.isStringLit then some ofL else none
    let lvls := ci.levelParams.map Level.param
    let ty := mkApp3 (mkConst ``Eq [1]) ci.type (mkConst cN lvls) val'
    let pf := mkApp2 (mkConst ``Eq.refl [1]) ci.type (mkConst cN lvls)
    CFSG.KC.addThmDecl <| { name := P ++ `eq, levelParams := ci.levelParams, type := ty, value := pf }

end
