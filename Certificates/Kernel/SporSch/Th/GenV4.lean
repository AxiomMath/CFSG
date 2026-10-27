module

public meta import Lean
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Data.CFSGNative.Th.Core
public import Certificates.Kernel.Sporadic.RawGen

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.Sporadic.Th.Native in
elab "#kss_v4rows " pre:ident cId:ident : command => do
  let cN ← liftCoreM <| realizeGlobalConstNoOverload cId
  let A ← liftTermElabM <| unsafe evalConst (Array V4) cN
  let vals := A.map fun v => v.w0.toNat ||| (v.w1.toNat <<< 64) ||| (v.w2.toNat <<< 128) |||
    (v.w3.toNat <<< 192)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree pre.getId vals

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kss_natlist " pre:ident cId:ident : command => do
  let cN ← liftCoreM <| realizeGlobalConstNoOverload cId
  let L ← liftTermElabM <| unsafe evalConst (List Nat) cN
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree pre.getId L.toArray

end
