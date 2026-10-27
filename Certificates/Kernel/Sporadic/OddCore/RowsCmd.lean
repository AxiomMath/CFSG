module

public meta import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public meta import Lean
public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.PEnumGen in
elab "#krows " pre:ident sId:ident : command => do
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let a ← liftTermElabM <| unsafe evalConst (Array Nat) sN
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree pre.getId (rows32 a)

end
