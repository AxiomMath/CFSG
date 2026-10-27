module

public import Certificates.Data.CFSGNative.Fi23.CentralizerData
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.Tab
public import Lean.Exception

public section

open Lean Elab Command CFSG.KC.Tab

namespace CertificateChecks.KernelLC.NatsGen

elab "#lc_natsof " pre:ident fId:ident : command => do
  let P := pre.getId
  let fN ← liftCoreM <| realizeGlobalConstNoOverload fId
  let env ← getEnv
  let s ← match (env.find? fN).bind ConstantInfo.value? with
    | some (.app (.const ``CFSG.Sporadic.Fi23.Native.natsOf _) (.lit (.strVal s))) => pure s
    | _ => throwError "#lc_natsof: {fN} is not `natsOf` of a string literal"
  let charE : Expr := mkConst ``Char
  let mk (ch : Char) : Expr := mkApp (mkConst ``Char.ofNat) (mkRawNatLit ch.toNat)
  let lst := s.toList.foldr (fun ch acc => mkApp3 (mkConst ``List.cons [0]) charE (mk ch) acc)
    (mkApp (mkConst ``List.nil [0]) charE)
  let lty := mkApp (mkConst ``List [0]) charE
  let arrE := mkApp (mkConst ``Array [0]) (mkConst ``Nat)
  withSync do
    addDef (P ++ `chars) lty lst
    let rhs := mkApp (mkConst ``CFSG.Sporadic.Fi23.Native.natsOf)
      (mkApp (mkConst ``String.ofList) (mkConst (P ++ `chars)))
    let ty := mkApp3 (mkConst ``Eq [1]) arrE (mkConst fN) rhs
    let pf := mkApp2 (mkConst ``Eq.refl [1]) arrE (mkConst fN)
    CFSG.KC.addThmDecl <| { name := P ++ `eq, levelParams := [], type := ty, value := pf }

end CertificateChecks.KernelLC.NatsGen

end
