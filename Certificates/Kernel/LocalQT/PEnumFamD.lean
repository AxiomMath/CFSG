module

public meta import Certificates.Kernel.LocalQT.PEnumD
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Lean
public import Certificates.Data.Kernel.Spor.PEnum
public import Certificates.Data.Kernel.Spor.HexAt
public import Certificates.Kernel.LocalQT.PEnumD

public section

namespace CFSG.KS.PEnumFamDGen

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.PEnumD CFSG.PSL3Four.Native

meta def penumFamD (n w : Nat) (conj : Bool) (gens ginv roots : Array (Array Nat)) (cap : Nat) :
    Array (Lean.Name × Array Nat) × Array (Lean.Name × Nat) := Id.run do
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
    let E := CFSG.PSL3Four.Native.bfs step k root cap
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
  return (#[(`T, tabs), (`TO, tOff), (`PL, rows32 pls), (`PLO, plO), (`POS, rows32 poss),
    (`POSO, posO), (`SRT, rows32 srts), (`SRTO, srtO), (`SRI, rows32 sris), (`SRIO, sriO),
    (`C, cnts), (`R, roots.map (pack w)), (`G, gens.map (pack w)), (`GI, ginv.map (pack w))],
    #[(`k, k), (`m, roots.size)])

meta def treeIn (d : Array (Lean.Name × Array Nat) × Array (Lean.Name × Nat)) (nm : Lean.Name) :
    Array Nat :=
  ((d.1.find? (·.1 == nm)).map (·.2)).getD #[]

meta def natStep (d : Array (Lean.Name × Array Nat) × Array (Lean.Name × Nat)) :
    CFSG.KC.Eval.Step :=
  fun _ => return d.2.map fun (nm, v) => (nm, .nat v)

end CFSG.KS.PEnumFamDGen

end
