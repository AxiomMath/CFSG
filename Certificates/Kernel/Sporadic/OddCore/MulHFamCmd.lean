module

public meta import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public meta import Certificates.Data.CFSGNative.SmallOddCore.Check
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Lean
public import CFSG.Certificates.Kernel.Spor.MulHSound
public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd

public section

namespace CFSG.KS.MulHFamGen

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.PEnumGen CFSG.PSL3Four.Native

meta def mulhFam (n w : Nat) (gensA ginvA : Array (Array (Array Nat))) (roots : Array (Array Nat))
    (cap : Nat) : Array (Lean.Name × Array Nat) × Array (Lean.Name × Nat) :=
  let inv : Nat → Array Nat → Array Nat := fun cnt s => Id.run do
    let mut r := Array.replicate cnt 0
    for i in [0:cnt] do
      r := r.set! s[i]! i
    return r
  let recs := (List.range roots.size).toArray.map fun r =>
    let gens := gensA[r]!
    let ginv := ginvA[r]!
    let k := gens.size
    let step : Nat → Tab → Tab := fun j t => conjTab n gens[j]! ginv[j]! t
    let E := CFSG.PSL3Four.Native.bfs step k roots[r]! cap
    let cnt := E.tabs.size
    let idx := indexOf E.tabs
    let pl := (List.range cnt).toArray.map fun i => 4096 * E.par[i]! + E.lab[i]!
    let pos := ((List.range cnt).toArray.map fun h =>
      (List.range k).toArray.map fun j => idx.getD (step j E.tabs[h]!) cnt).flatten
    let keys := E.tabs.map (pack w)
    let srt := ((List.range cnt).toArray.qsort fun a b => keys[a]! < keys[b]!)
    let hk := E.tabs.map fun t =>
      (CFSG.Sporadic.SmallOddCore.Native.hkey n (t.map UInt32.ofNat)).toNat
    let hs := ((List.range cnt).toArray.qsort fun a b => hk[a]! < hk[b]!)
    (keys, gens.map (pack w), ginv.map (pack w), pack w roots[r]!, pl, pos, srt, inv cnt srt, hs,
      inv cnt hs, cnt, k)
  let ts := recs.foldl (fun m e => max m (max e.2.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.2.2)) 1
  let rr := (ts + 31) / 32
  let pr := (recs.foldl (fun m e => max m e.2.2.2.2.2.1.size) 1 + 31) / 32
  let pad : Nat → Array Nat → Array Nat := fun len a => (List.range len).toArray.map fun i => a.getD i 0
  let tabs := (recs.map fun e => pad ts e.1).flatten
  let gs := (recs.map fun e => pad ts e.2.1).flatten
  let gis := (recs.map fun e => pad ts e.2.2.1).flatten
  let rowsOf : (Array Nat) → Nat → Array Nat := fun a len => rows32 (pad (32 * len) a)
  (#[(`T, tabs), (`G, gs), (`GI, gis), (`R, recs.map fun e => e.2.2.2.1),
    (`PL, (recs.map fun e => rowsOf e.2.2.2.2.1 rr).flatten),
    (`POS, (recs.map fun e => rowsOf e.2.2.2.2.2.1 pr).flatten),
    (`SRT, (recs.map fun e => rowsOf e.2.2.2.2.2.2.1 rr).flatten),
    (`SRI, (recs.map fun e => rowsOf e.2.2.2.2.2.2.2.1 rr).flatten),
    (`HS, (recs.map fun e => rowsOf e.2.2.2.2.2.2.2.2.1 rr).flatten),
    (`HSI, (recs.map fun e => rowsOf e.2.2.2.2.2.2.2.2.2.1 rr).flatten),
    (`cnt, recs.map fun e => e.2.2.2.2.2.2.2.2.2.2.1),
    (`k, recs.map fun e => e.2.2.2.2.2.2.2.2.2.2.2)],
   #[(`ts, ts), (`rr, rr), (`pr, pr), (`nr, recs.size)])

meta def treeIn (d : Array (Lean.Name × Array Nat) × Array (Lean.Name × Nat)) (nm : Lean.Name) :
    Array Nat :=
  ((d.1.find? (·.1 == nm)).map (·.2)).getD #[]

meta def natStep (d : Array (Lean.Name × Array Nat) × Array (Lean.Name × Nat)) :
    CFSG.KC.Eval.Step :=
  fun _ => return d.2.map fun (nm, v) => (nm, .nat v)

end CFSG.KS.MulHFamGen

end
