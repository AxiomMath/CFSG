module

public meta import Lean
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public import Certificates.Kernel.Sporadic.RawGen

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kss_perms " pre:ident ww:num aId:ident : command => do
  let aN ← liftCoreM <| realizeGlobalConstNoOverload aId
  let A ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) aN
  let P := pre.getId
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree P (A.map (pack ww.getNat))
    addDef (P ++ `cnt) natT (lit A.size)

end
