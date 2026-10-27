module

public import Certificates.Kernel.Sporadic.ON.Gen
public meta import Certificates.Kernel.Sporadic.ON.Gen

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.ONGen in
elab "#kon_words " pre:ident wId:ident : command => do
  let P := pre.getId
  let wN ← liftCoreM <| realizeGlobalConstNoOverload wId
  let ws ← liftTermElabM <| unsafe evalConst (Array (List Int)) wN
  withSync do
    addTree (P ++ `WC) (ws.map encW)
    addTree (P ++ `WL) (ws.map (·.length))
    addDef (P ++ `N) natT (lit ws.size)

end
