module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import CFSG.Certificates.Kernel.Common.StrLits
public import CFSG.Certificates.Kernel.Common.StrLits
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.Tab

open Lean Elab Command Meta

open CFSG.KC.Tab in
elab "#ks_chars_lits " pre:ident sId:ident : command => do
  let P := pre.getId
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let some body := ((← getEnv).find? sN).bind ConstantInfo.value?
    | throwError "#ks_chars_lits: `{sN}` has no visible definition"
  let (L, h) ← liftTermElabM <| CFSG.KC.StrLits.build body none
  let s ← liftTermElabM <| unsafe evalConst String sN
  let lty := mkApp (mkConst ``List [0]) (mkConst ``Char)
  let strE := mkConst ``String
  withSync do
    addDef (P ++ `chars) lty (CFSG.KC.StrLits.charsE s)
    let ty := mkApp3 (mkConst ``Eq [1]) strE (mkConst sN)
      (mkApp (mkConst ``String.ofList) (mkConst (P ++ `chars)))
    let pf := mkApp4 (mkConst ``Eq.symm [1]) strE (mkApp (mkConst ``String.ofList) L) (mkConst sN) h
    CFSG.KC.addThmDecl <| { name := P ++ `eq, levelParams := [], type := ty, value := pf }
