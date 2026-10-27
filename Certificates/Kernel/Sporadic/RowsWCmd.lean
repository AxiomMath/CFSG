module

public meta import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public meta import Lean
public import Certificates.Kernel.Sporadic.RawGen

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#krowsw " pre:ident ww:num sId:ident : command => do
  let w := ww.getNat
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let a ← liftTermElabM <| unsafe evalConst (Array Nat) sN
  let rows := (List.range ((a.size + 31) / 32)).toArray.map fun r =>
    pack w ((List.range 32).toArray.map fun t => a.getD (32 * r + t) 0)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree pre.getId rows

end
