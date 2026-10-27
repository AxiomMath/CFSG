module

public meta import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public meta import Certificates.Data.CFSGNative.Perm.Chain
public meta import Lean
public import CFSG.Certificates.Kernel.Spor.TBfsSound
public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.PEnumGen CFSG.Perm.Native CFSG.Sporadic.Th.Native in
elab "#ktbfs " pre:ident nn:num rr:num lId:ident lvId:ident : command => do
  let P := pre.getId
  let n := nn.getNat
  let root := rr.getNat
  let lN ← liftCoreM <| realizeGlobalConstNoOverload lId
  let lvN ← liftCoreM <| realizeGlobalConstNoOverload lvId
  let letters ← liftTermElabM <| unsafe evalConst (Array Table) lN
  let lv ← liftTermElabM <| unsafe evalConst (Array Nat) lvN
  let T := treeBFS n root letters lv
  let cnt := T.pts.size
  let ti := (List.range cnt).toArray.map fun k =>
    if k == 0 then 0 else (lv.toList.idxOf (T.lab[k]!).toNat)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `PTS) (rows32 (T.pts.map (·.toNat)))
    addTree (P ++ `POS) (rows32 (T.pos.map (·.toNat)))
    addTree (P ++ `PAR) (rows32 (T.par.map (·.toNat)))
    addTree (P ++ `LAB) (rows32 (T.lab.map (·.toNat)))
    addTree (P ++ `TI) (rows32 ti)
    addDef (P ++ `cnt) natT (lit cnt)

end
