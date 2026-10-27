module

public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Lean
public import Certificates.Data.Kernel.Spor.BTupR
public import Certificates.Kernel.Sporadic.RawGen
public import Lean.Exception

open Lean Elab Command

public section

namespace CFSG.KS.BTupRGen

open CFSG.KS.RawGen

meta def rowsW (fw : Nat) (a : Array Nat) : Array Nat :=
  (List.range ((a.size + 31) / 32)).toArray.map fun r =>
    pack fw ((List.range 32).toArray.map fun t => a.getD (32 * r + t) 0)

meta def bfs (w : Nat) (gens : Array (Array Nat)) (base : Array Nat) :
    Array (Array Nat) × Array Nat × Array Nat := Id.run do
  let key : Array Nat → Nat := pack w
  let mut sts : Array (Array Nat) := #[base]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut idx : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert (key base) 0
  let mut q := 0
  while q < sts.size do
    let t := sts[q]!
    for j in [0:gens.size] do
      let u := t.map fun x => gens[j]![x]!
      let ku := key u
      if !idx.contains ku then
        idx := idx.insert ku sts.size
        sts := sts.push u
        par := par.push q
        lab := lab.push j
    q := q + 1
  return (sts, par, lab)

public meta def treeIn (d : Except String (Array (Name × Array Nat) × Array (Name × Nat)))
    (nm : Name) : Array Nat :=
  match d with
  | .ok (ts, _) => ((ts.find? (·.1 == nm)).map (·.2)).getD #[]
  | .error _ => #[]

public meta def natStep (d : Except String (Array (Name × Array Nat) × Array (Name × Nat))) :
    CFSG.KC.Eval.Step := fun _ => do
  let (_, ns) ← d
  return ns.map fun (nm, v) => (nm, .nat v)

public meta def ruData (n w : Nat) (gens : Array (Array Nat)) (base : Array Nat)
    (ys tgens : Array (Array Nat)) :
    Except String (Array (Name × Array Nat) × Array (Name × Nat)) := do
  if base.any (· ≥ n) then throw s!"ruData: a base point is not below {n}"
  let key : Array Nat → Nat := pack w
  let k := gens.size
  let m := ys.size
  let (sts, par, lab) := bfs w gens base
  let cnt := sts.size
  let keys := sts.map key
  let srt := (List.range cnt).toArray.qsort fun a b => keys[a]! < keys[b]!
  let mut pos := Array.replicate cnt 0
  for s in [0:cnt] do
    pos := pos.set! srt[s]! s
  let mut idx : Std.HashMap Nat Nat := {}
  for i in [0:cnt] do
    idx := idx.insert keys[i]! i
  let stOf (u : Array Nat) : Except String Nat :=
    match idx.get? (key u) with
    | some i => pure i
    | none => throw "ruData: a tuple is not in the orbit"
  let mut sY : Array Nat := #[]
  for j in [0:m] do
    sY := sY.push (← stOf (base.map fun x => ys[j]![x]!))
  let mut rt : Array (Array Nat) := Array.replicate cnt #[]
  for i in [0:cnt] do
    if i == 0 then
      rt := rt.set! 0 sY
    else
      let p := par[i]!
      let l := lab[i]!
      let row ← (rt[p]!).mapM fun q => stOf (sts[q]!.map fun x => gens[l]![x]!)
      rt := rt.set! i row
  let (tsts, _, _) := bfs w tgens base
  let tkeys := (tsts.map key).qsort (· < ·)
  let mut tidx : Std.HashMap Nat Nat := {}
  for s in [0:tkeys.size] do
    tidx := tidx.insert tkeys[s]! s
  let mut ix := Array.replicate cnt 0
  for i in [0:cnt] do
    let cz := (List.range m).all fun j =>
      keys[rt[i]![j]!]! == key (sts[i]!.map fun x => ys[j]![x]!)
    if cz then
      match tidx.get? keys[i]! with
      | some s => ix := ix.set! pos[i]! s
      | none => throw "ruData: a state commuting with every y is not in the target orbit"
  let mut sT : Array Nat := #[]
  for j in [0:tgens.size] do
    sT := sT.push pos[← stOf (base.map fun x => tgens[j]![x]!)]!
  let rtS := (srt.map fun i => (rt[i]!).map fun q => pos[q]!).flatten
  let _ := k
  return (#[(`S, sY.map fun i => pos[i]!), (`T, sT), (`RT, rowsW 32 rtS), (`IX, rowsW 32 ix)], #[])

end CFSG.KS.BTupRGen

end
