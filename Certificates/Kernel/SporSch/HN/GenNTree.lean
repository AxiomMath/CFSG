module

public meta import Lean
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public import Certificates.Kernel.Sporadic.RawGen

open Lean Elab Command

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kss_ntree " pre:ident vId:ident : command => do
  let vN ← liftCoreM <| realizeGlobalConstNoOverload vId
  let vs ← liftTermElabM <| unsafe evalConst (List Nat) vN
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree pre.getId vs.toArray
