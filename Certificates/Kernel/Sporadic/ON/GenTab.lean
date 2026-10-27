module

public import Certificates.Kernel.Sporadic.ON.Gen
public meta import Certificates.Kernel.Sporadic.ON.Gen

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.ONGen in
elab "#kon_table " pre:ident tId:ident : command => do
  let tN ← liftCoreM <| realizeGlobalConstNoOverload tId
  let t ← liftTermElabM <| unsafe evalConst (Array Nat) tN
  withSync do
    addTree pre.getId (leaves 18 6 t)

end
