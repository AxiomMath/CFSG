module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import CFSG.Certificates.Kernel.Common.StrLits
public import CFSG.Certificates.Kernel.Common.StrLits
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.Tab

open Lean Elab Command Meta

meta partial def leaves (t : Expr) : String :=
  match t.consumeMData with
  | .lit (.strVal s) => s
  | t' => match CFSG.KC.StrLits.appendArgs? t' with
    | some (a, b) => leaves a ++ leaves b
    | none => ""

open CFSG.KC.Tab in
elab "#ks_chars_fn " pre:ident fId:ident : command => do
  let P := pre.getId
  let fN ← liftCoreM <| realizeGlobalConstNoOverload fId
  let some body := ((← getEnv).find? fN).bind ConstantInfo.value?
    | throwError "#ks_chars_fn: `{fN}` has no visible definition"
  let .lam _ _ t _ := body.consumeMData
    | throwError "#ks_chars_fn: `{fN}` is not a function of one argument"
  if t.hasLooseBVars then throwError "#ks_chars_fn: the body of `{fN}` uses its argument"
  let (L, h) ← liftTermElabM <| CFSG.KC.StrLits.build t none
  let s := leaves t
  let lty := mkApp (mkConst ``List [0]) (mkConst ``Char)
  let strE := mkConst ``String
  let fApp := mkApp (mkConst fN) (mkConst ``Unit.unit)
  withSync do
    addDef (P ++ `chars) lty (CFSG.KC.StrLits.charsE s)
    let ty := mkApp3 (mkConst ``Eq [1]) strE fApp
      (mkApp (mkConst ``String.ofList) (mkConst (P ++ `chars)))
    let pf := mkApp4 (mkConst ``Eq.symm [1]) strE (mkApp (mkConst ``String.ofList) L) fApp h
    CFSG.KC.addThmDecl <| { name := P ++ `eq, levelParams := [], type := ty, value := pf }
