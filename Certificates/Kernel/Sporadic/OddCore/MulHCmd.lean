module

public meta import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public meta import Certificates.Data.CFSGNative.SmallOddCore.Check
public meta import Lean
public import CFSG.Certificates.Kernel.Spor.MulHSound
public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.PEnumGen CFSG.PSL3Four.Native in
elab "#kmulh " pre:ident nn:num ww:num gId:ident giId:ident rId:ident cp:num : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let cap := cp.getNat
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let giN ← liftCoreM <| realizeGlobalConstNoOverload giId
  let rN ← liftCoreM <| realizeGlobalConstNoOverload rId
  let gens ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) gN
  let ginv ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) giN
  let root ← liftTermElabM <| unsafe evalConst (Array Nat) rN
  let k := gens.size
  let step : Nat → Tab → Tab := fun j t => conjTab n gens[j]! ginv[j]! t
  let E := bfs step k root cap
  let cnt := E.tabs.size
  let idx := indexOf E.tabs
  let pl := (List.range cnt).toArray.map fun i => 4096 * E.par[i]! + E.lab[i]!
  let pos := ((List.range cnt).toArray.map fun h =>
    (List.range k).toArray.map fun j => idx.getD (step j E.tabs[h]!) cnt).flatten
  let keys := E.tabs.map (pack w)
  let srt := ((List.range cnt).toArray.qsort fun a b => keys[a]! < keys[b]!)
  let inv : Array Nat → Array Nat := fun s => Id.run do
    let mut r := Array.replicate cnt 0
    for i in [0:cnt] do
      r := r.set! s[i]! i
    return r
  let hk := E.tabs.map fun t =>
    (CFSG.Sporadic.SmallOddCore.Native.hkey n (t.map UInt32.ofNat)).toNat
  let hs := ((List.range cnt).toArray.qsort fun a b => hk[a]! < hk[b]!)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `T) keys
    addTree (P ++ `G) (gens.map (pack w))
    addTree (P ++ `GI) (ginv.map (pack w))
    addDef (P ++ `R) natT (lit (pack w root))
    addTree (P ++ `PL) (rows32 pl)
    addTree (P ++ `POS) (rows32 pos)
    addTree (P ++ `SRT) (rows32 srt)
    addTree (P ++ `SRI) (rows32 (inv srt))
    addTree (P ++ `HS) (rows32 hs)
    addTree (P ++ `HSI) (rows32 (inv hs))
    addDef (P ++ `cnt) natT (lit cnt)
    addDef (P ++ `k) natT (lit k)

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.PEnumGen CFSG.PSL3Four.Native in
elab "#kfind " pre:ident rId:ident qId:ident : command => do
  let rN ← liftCoreM <| realizeGlobalConstNoOverload rId
  let qN ← liftCoreM <| realizeGlobalConstNoOverload qId
  let rec_ ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) rN
  let qs ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) qN
  let idx := indexOf rec_
  let pos := qs.map fun q => idx.getD q rec_.size
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree pre.getId (rows32 pos)

end
