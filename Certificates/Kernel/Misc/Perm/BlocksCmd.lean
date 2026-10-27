module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.Kernel.ConjOrb
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kmisc_blocks " pre:ident cId:ident bb:num : command => do
  let P := pre.getId
  let bw := bb.getNat
  let cN ← liftCoreM <| realizeGlobalConstNoOverload cId
  let vs ← liftTermElabM <| unsafe evalConst (Array Nat) cN
  let leaves := (Array.range ((vs.size + 63) / 64)).map fun b => Id.run do
    let mut acc := 0
    for t in [0:64] do
      let k := 64 * b + t
      if k < vs.size then
        acc := acc ||| (vs[k]! <<< (bw * t))
    return acc
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `L) leaves
    addDef P fnT (mkApp2 (mkConst ``CFSG.KC.ConjOrb.blk) (mkConst (P ++ `L)) (lit bw))

end
