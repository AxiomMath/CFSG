module

public meta import Certificates.Data.GH23Perm

public section

namespace CFSG.KC.Misc.A6AutGen

open CFSG.OddStandard.SmallF3.HarrisU33.GH23Data

meta def gens : Array Nat := #[16434369, 16354065]

meta def bfs : Array Nat × Array (Nat × Nat) := Id.run do
  let mut E : Array Nat := #[oneC]
  let mut P : Array (Nat × Nat) := #[(0, 0)]
  let mut idx : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert oneC 0
  let mut k := 0
  while k < E.size do
    for l in [0:2] do
      let h := mulC E[k]! gens[l]!
      if !idx.contains h then
        idx := idx.insert h E.size
        E := E.push h
        P := P.push (k, l)
    k := k + 1
  return (E, P)

meta def E : Array Nat := bfs.1

meta def idx : Std.HashMap Nat Nat :=
  (List.range E.size).foldl (fun m t => m.insert E[t]! t) {}

meta def pos (c : Nat) : Nat := idx.getD c 0

meta def sq (a : Nat) : Nat := mulC a a

meta def eL : List Nat := E.toList
meta def pL : List Nat := (bfs.2.map fun (p, l) => p + 2 ^ 24 * l).toList
meta def sL : List Nat := ((Array.range E.size).qsort fun a b => E[a]! < E[b]!).toList
meta def cL : List Nat := (List.range E.size).flatMap fun k => [0, 1].map fun j => pos (mulC E[k]! gens[j]!)

meta def l2 : Array Nat := (Array.range E.size).filter fun k => sq E[k]! == oneC
meta def l4 : Array Nat := (Array.range E.size).filter fun k => sq (sq E[k]!) == oneC
meta def l2L : List Nat := l2.toList
meta def l4L : List Nat := l4.toList
meta def r2L : List Nat := (List.range E.size).map fun k => (l2.findIdx? (· == k)).getD 0
meta def r4L : List Nat := (List.range E.size).map fun k => (l4.findIdx? (· == k)).getD 0

meta def table (u v : Nat) : Array Nat := Id.run do
  let mut T : Array Nat := #[oneC]
  for k in [1:E.size] do
    let (p, l) := bfs.2[k]!
    T := T.push (mulC T[p]! (if l == 0 then u else v))
  return T

meta def pow5 (a : Nat) : Nat := mulC a (mulC a (mulC a (mulC a a)))

meta def pack (c : List Nat) : Nat :=
  (c.zipIdx.foldl fun acc (f, i) => acc + f * 2 ^ (1 + 9 * i)) 0

meta def wit (iu iv : Nat) : Nat :=
  let u := E[iu]!
  let v := E[iv]!
  if pow5 (mulC u v) != oneC || pow5 (mulC u (sq v)) != oneC then 0 else
  let T := table u v
  if T[iu]! != gens[0]! || T[iv]! != gens[1]! || (u == gens[0]! && v == gens[1]!) then 0 else
  let n := E.size
  let invPos := fun g => (List.range n).find? (fun h => mulC E[g]! E[h]! == oneC) |>.getD 0
  match (List.range n).find? (fun g => let t := mulC T[g]! E[invPos g]!
      sq t != oneC && sq (sq t) == oneC) with
  | some g => pack [g, invPos g]
  | none =>
    let cand := (List.range n).filter fun a => mulC (sq E[a]!) E[a]! == oneC && E[a]! != oneC
    let ab := cand.flatMap fun ia => cand.filterMap fun ib =>
      let a := E[ia]!
      let b := E[ib]!
      if mulC a b == mulC b a && b != a && b != sq a &&
        ((T[ia]! == sq a && T[ib]! == b) || (T[ia]! == b && T[ib]! == a)) then some (ia, ib)
      else none
    let g := (List.range n).find? (fun g => let t := mulC T[g]! E[invPos g]!
      t != oneC && sq t == oneC) |>.getD 0
    match ab.head? with
    | some (ia, ib) => 1 + pack [g, invPos g, ia, ib]
    | none => 0

meta def wL : List Nat :=
  l2L.flatMap fun iu => l4L.map fun iv => wit iu iv

end CFSG.KC.Misc.A6AutGen

end
