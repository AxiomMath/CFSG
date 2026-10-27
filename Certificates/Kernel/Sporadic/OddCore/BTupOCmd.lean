module

public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.Sporadic.OddCore.BTupRCmd
public meta import Lean
public import Certificates.Data.Kernel.Spor.BTupO
public import Certificates.Kernel.Sporadic.OddCore.BTupRCmd

open Lean

public section

namespace CFSG.KS.BTupRGen

open CFSG.KS.RawGen

public meta def orbcData (n w : Nat) (gens : Array (Array Nat)) (base : Array Nat)
    (cgens : Array (Array Nat)) (root : Array Nat) :
    Except String (Array (Name × Array Nat) × Array (Name × Nat)) := do
  if base.any (· ≥ n) then throw s!"orbcData: a base point is not below {n}"
  let key : Array Nat → Nat := pack w
  let d := base.size
  let (sts, par, lab) := bfs w gens base
  let cnt := sts.size
  let keys := sts.map key
  let mut idx : Std.HashMap Nat Nat := {}
  for i in [0:cnt] do
    idx := idx.insert keys[i]! i
  let stOf (u : Array Nat) : Except String Nat :=
    match idx.get? (key u) with
    | some i => pure i
    | none => throw "orbcData: a tuple is not in the orbit"
  let mut els : Array (Array Nat) := Array.replicate cnt (Array.range n)
  for i in [1:cnt] do
    let g := gens[lab[i]!]!
    let xp := els[par[i]!]!
    els := els.set! i (xp.map fun p => g[p]!)
  let srt := (List.range cnt).toArray.qsort fun a b => keys[a]! < keys[b]!
  let mut pos := Array.replicate cnt 0
  for s in [0:cnt] do
    pos := pos.set! srt[s]! s
  let mut cinv : Array (Array Nat) := #[]
  for c in cgens do
    let mut ci := Array.replicate n 0
    for x in [0:n] do
      ci := ci.set! c[x]! x
    cinv := cinv.push ci
  let pre := (cinv.map fun ci => base.map fun b => ci[b]!).flatten
  let r ← stOf (base.map fun b => root[b]!)
  let mut tg : Array Nat := Array.replicate cnt 0
  let mut dep : Array Nat := Array.replicate cnt 0
  let mut inO : Array Bool := Array.replicate cnt false
  inO := inO.set! r true
  tg := tg.set! pos[r]! 1
  let mut queue : Array Nat := #[r]
  let mut q := 0
  while q < queue.size do
    let s := queue[q]!
    for j in [0:cgens.size] do
      let c := cgens[j]!
      let u ← stOf (base.map fun b => c[els[s]![cinv[j]![b]!]!]!)
      if !inO[u]! then
        inO := inO.set! u true
        dep := dep.set! u (dep[s]! + 1)
        tg := tg.set! pos[u]! (1 + 2 * j + 512 * pos[s]! + 2199023255552 * (dep[s]! + 1))
        queue := queue.push u
    q := q + 1
  let _ := d
  return (#[(`C, cgens.map (pack w)), (`PRE, rowsW 16 pre), (`TG, rowsW 64 tg)],
    #[(`cnt, queue.size)])

end CFSG.KS.BTupRGen

end
