module

public meta import Lean
public meta import Certificates.Data.YamakiPres
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.KD.YamakiRep.Gen

open CFSG.ClassicalInvolution.Solomon73.Yamaki

meta def numM (i : Fin 12) : Nat :=
  (List.finRange 6).foldl (fun acc r => (List.finRange 6).foldl (fun acc c =>
    acc ||| ((yamakiMat6 i r c).val <<< (6 * r.val + c.val))) acc) 0

meta def mulM (A B : Nat) : Nat := Id.run do
  let mut r := 0
  for i in [0:6] do
    let mut row := 0
    for k in [0:6] do
      if (A >>> (6 * i + k)) &&& 1 == 1 then
        row := row ^^^ ((B >>> (6 * k)) &&& 63)
    r := r ||| (row <<< (6 * i))
  return r

meta def oneM : Nat := 34630287489

meta def gM : Array Nat := ((List.finRange 12).map numM).toArray

meta def wordM (w : List Nat) : Nat := w.foldr (fun i acc => mulM gM[i]! acc) oneM

meta def bfsM (gs : Array Nat) (fuel : Nat) :
    Array Nat × Array (Nat × Nat) × Array Nat × Array Nat := Id.run do
  let mut es : Array Nat := #[oneM]
  let mut par : Array (Nat × Nat) := #[]
  let mut idx : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert oneM 0
  let mut C : Array Nat := #[]
  let mut POS : Array Nat := #[]
  for h in [0:fuel] do
    if h < es.size then
      for s in [0:gs.size] do
        C := C.push es.size
        let y := mulM es[h]! gs[s]!
        match idx.get? y with
        | some p => POS := POS.push p
        | none =>
          POS := POS.push es.size
          idx := idx.insert y es.size
          es := es.push y
          par := par.push (h, s)
  C := C.push es.size
  return (es, par, C, POS)

meta def sortM (xs : Array Nat) : Array Nat × Array Nat :=
  let srt := (Array.range xs.size).qsort (fun a b => xs[a]! < xs[b]!)
  let sri := (Array.range srt.size).foldl (fun acc i => acc.set! srt[i]! i)
    (Array.replicate srt.size 0)
  (srt, sri)

meta def recsFor (gs : Array Nat) (n : Nat) : Except String (List Nat) := do
  let (es, par, C, POS) := bfsM gs n
  if es.size != n then throw s!"the table has {es.size} matrices, not {n}"
  let (srt, sri) := sortM es
  let k := gs.size
  let f := fun (v : Nat) (i : Nat) => v <<< (64 + 16 * i)
  let recs := (List.range (n + 1)).map fun t =>
    let p := par.getD t (0, 0)
    let base := es.getD t 0 ||| f p.1 0 ||| f p.2 1 ||| f (srt.getD t 0) 2 |||
      f (sri.getD t 0) 3
    (List.range k).foldl (fun acc s =>
      acc ||| f (C.getD (k * t + s) 0) (4 + s) ||| f (POS.getD (k * t + s) 0) (4 + k + s)) base
  return gM.toList ++ gs.toList ++ recs

meta def recsW (ws : List (List Nat)) (n : Nat) : List Nat :=
  match recsFor (ws.map wordM).toArray n with
  | .ok l => l
  | .error e => panic! e

meta def recsI (is : List Nat) (n : Nat) : List Nat :=
  match recsFor (is.map fun i => gM[i]!).toArray n with
  | .ok l => l
  | .error e => panic! e

end CFSG.KD.YamakiRep.Gen

end
