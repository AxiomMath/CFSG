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
elab "#kpenumgens " pre:ident nn:num ww:num gId:ident cId:ident : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let cN ← liftCoreM <| realizeGlobalConstNoOverload cId
  let fam ← liftTermElabM <| unsafe evalConst (Array (Array (Array Nat))) gN
  let caps ← liftTermElabM <| unsafe evalConst (Array Nat) cN
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
  let mut gs : Array Nat := #[]
  let mut gO : Array Nat := #[]
  let mut ks : Array Nat := #[]
  for l in [0:fam.size] do
    let gens := fam[l]!
    let k := gens.size
    let step : Nat → Tab → Tab := fun j t => CFSG.PSL3Four.Native.comp n gens[j]! t
    let E := bfs step k (idTab n) caps[l]!
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
    gO := gO.push gs.size
    gs := gs ++ gens.map (pack w)
    ks := ks.push k
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
    addTree (P ++ `G) gs
    addTree (P ++ `GO) gO
    addTree (P ++ `K) ks
    addDef (P ++ `m) natT (lit fam.size)

end
