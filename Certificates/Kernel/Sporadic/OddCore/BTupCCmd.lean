module

public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.Sporadic.OddCore.BTupRCmd
public meta import Lean
public import Certificates.Data.Kernel.Spor.BTupM
public import Certificates.Kernel.Sporadic.OddCore.BTupRCmd

open Lean

public section

namespace CFSG.KS.BTupRGen

open CFSG.KS.RawGen

public meta def clsData (n w : Nat) (gens : Array (Array Nat)) (base : Array Nat)
    (lgens : Array (Array Nat)) :
    Except String (Array (Name × Array Nat) × Array (Name × Nat)) := do
  if base.any (· ≥ n) then throw s!"clsData: a base point is not below {n}"
  let key : Array Nat → Nat := pack w
  let k := gens.size
  let (sts, par, lab) := bfs w gens base
  let cnt := sts.size
  let keys := sts.map key
  let mut idx : Std.HashMap Nat Nat := {}
  for i in [0:cnt] do
    idx := idx.insert keys[i]! i
  let stOf (u : Array Nat) : Except String Nat :=
    match idx.get? (key u) with
    | some i => pure i
    | none => throw "clsData: a tuple is not in the orbit"
  let mut sY : Array Nat := #[]
  for j in [0:k] do
    sY := sY.push (← stOf (base.map fun x => gens[j]![x]!))
  let mut rt : Array (Array Nat) := Array.replicate cnt #[]
  for i in [0:cnt] do
    if i == 0 then
      rt := rt.set! 0 sY
    else
      let row ← (rt[par[i]!]!).mapM fun q => stOf (sts[q]!.map fun x => gens[lab[i]!]![x]!)
      rt := rt.set! i row
  let mul (a q : Nat) : Nat := Id.run do
    let mut a := a
    let mut q := q
    while q != 0 do
      a := rt[a]![lab[q]!]!
      q := par[q]!
    return a
  let mut sI : Array Nat := #[]
  for j in [0:k] do
    let g := gens[j]!
    let mut gi := Array.replicate n 0
    for x in [0:n] do
      gi := gi.set! g[x]! x
    sI := sI.push (← stOf (base.map fun x => gi[x]!))
  let mut inv : Array Nat := Array.replicate cnt 0
  for i in [1:cnt] do
    inv := inv.set! i (mul inv[par[i]!]! sI[lab[i]!]!)
  let srt := (List.range cnt).toArray.qsort fun a b => keys[a]! < keys[b]!
  let mut pos := Array.replicate cnt 0
  for s in [0:cnt] do
    pos := pos.set! srt[s]! s
  let (lsts, _, _) := bfs w lgens base
  let lkeys := (lsts.map key).qsort (· < ·)
  let mut lidx : Std.HashMap Nat Nat := {}
  for s in [0:lkeys.size] do
    lidx := lidx.insert lkeys[s]! s
  let mut tg := Array.replicate cnt 0
  let mut ents : Array Nat := #[]
  let mut ne := 0
  for i in [0:cnt] do
    match lidx.get? keys[i]! with
    | some p => tg := tg.set! pos[i]! (4 * p)
    | none =>
      if mul i i != 0 then
        tg := tg.set! pos[i]! 1
      else
        let mut seen : Std.HashMap Nat Nat := {}
        let mut g := 0
        while seen.size < 9 && g < cnt do
          let c := mul (mul g i) inv[g]!
          if !seen.contains c then
            seen := seen.insert c g
          g := g + 1
        if seen.size < 9 then throw "clsData: an involution has fewer than 9 conjugates"
        let prs := (seen.toArray.map fun (c, g) => (pos[c]!, pos[g]!)).qsort fun a b => a.1 < b.1
        ents := ents.push pos[i]! ++ prs.map (·.2) ++ prs.map (·.1)
        tg := tg.set! pos[i]! (2 + 4 * ne)
        ne := ne + 1
  return (#[(`TG, rowsW 32 tg), (`E, rowsW 16 ents)], #[(`r0, pos[0]!), (`ne, ne)])

end CFSG.KS.BTupRGen

end
