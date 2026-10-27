module

public meta import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import Lean
public import CFSG.Certificates.Kernel.Spor.PEnumSound
public import Certificates.Data.Kernel.Spor.HexAt
public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.PEnumGen CFSG.PSL3Four.Native in
elab "#kpenumfam " pre:ident nn:num ww:num cj:ident gId:ident giId:ident rId:ident cp:num :
    command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let conj := cj.getId == `true
  let cap := cp.getNat
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let giN ← liftCoreM <| realizeGlobalConstNoOverload giId
  let rN ← liftCoreM <| realizeGlobalConstNoOverload rId
  let gens ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) gN
  let ginv ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) giN
  let roots ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) rN
  let k := gens.size
  let step : Nat → Tab → Tab := fun j t =>
    if conj then conjTab n gens[j]! ginv[j]! t else CFSG.PSL3Four.Native.comp n gens[j]! t
  let pad := fun (a : Array Nat) => a ++ Array.replicate ((32 - a.size % 32) % 32) 0
  let mut tabs : Array Nat := #[]
  let mut tOff : Array Nat := #[]
  let mut pls : Array Nat := #[]
  let mut poss : Array Nat := #[]
  let mut srts : Array Nat := #[]
  let mut sris : Array Nat := #[]
  let mut plO : Array Nat := #[]
  let mut posO : Array Nat := #[]
  let mut srtO : Array Nat := #[]
  let mut sriO : Array Nat := #[]
  let mut cnts : Array Nat := #[]
  for root in roots do
    let E := bfs step k root cap
    let cnt := E.tabs.size
    let idx := indexOf E.tabs
    let keys := E.tabs.map (pack w)
    let pl := (List.range cnt).toArray.map fun i => 4096 * E.par[i]! + E.lab[i]!
    let pos := ((List.range cnt).toArray.map fun h =>
      (List.range k).toArray.map fun j => idx.getD (step j E.tabs[h]!) cnt).flatten
    let srt := ((List.range cnt).toArray.qsort fun a b => keys[a]! < keys[b]!)
    let sri := Id.run do
      let mut r := Array.replicate cnt 0
      for s in [0:cnt] do
        r := r.set! srt[s]! s
      return r
    tOff := tOff.push tabs.size
    tabs := tabs ++ keys
    plO := plO.push (pls.size / 32)
    pls := pls ++ pad pl
    posO := posO.push (poss.size / 32)
    poss := poss ++ pad pos
    srtO := srtO.push (srts.size / 32)
    srts := srts ++ pad srt
    sriO := sriO.push (sris.size / 32)
    sris := sris ++ pad sri
    cnts := cnts.push cnt
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `T) tabs
    addTree (P ++ `TO) tOff
    addTree (P ++ `PL) (rows32 pls)
    addTree (P ++ `PLO) plO
    addTree (P ++ `POS) (rows32 poss)
    addTree (P ++ `POSO) posO
    addTree (P ++ `SRT) (rows32 srts)
    addTree (P ++ `SRTO) srtO
    addTree (P ++ `SRI) (rows32 sris)
    addTree (P ++ `SRIO) sriO
    addTree (P ++ `C) cnts
    addTree (P ++ `R) (roots.map (pack w))
    addTree (P ++ `G) (gens.map (pack w))
    addTree (P ++ `GI) (ginv.map (pack w))
    addDef (P ++ `k) natT (lit k)
    addDef (P ++ `m) natT (lit roots.size)

end
