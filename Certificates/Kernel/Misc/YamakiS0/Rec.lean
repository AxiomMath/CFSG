module

public meta import Lean
meta import Certificates.Data.YamakiPres
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

namespace CFSG.KD.YamakiS0.Gen

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

meta def bfsM (start : Nat) (st : Nat → Nat → Nat) (k fuel : Nat) :
    Array Nat × Array (Nat × Nat) × Array Nat × Array Nat := Id.run do
  let mut es : Array Nat := #[start]
  let mut par : Array (Nat × Nat) := #[]
  let mut idx : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert start 0
  let mut C : Array Nat := #[]
  let mut POS : Array Nat := #[]
  for h in [0:fuel] do
    if h < es.size then
      for s in [0:k] do
        C := C.push es.size
        let y := st es[h]! s
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

meta def recsM (k : Nat) (b : Array Nat × Array (Nat × Nat) × Array Nat × Array Nat)
    (w : Nat → Nat) : List Nat :=
  let (es, par, C, POS) := b
  let (srt, sri) := sortM es
  let n := es.size
  let f := fun (v : Nat) (i : Nat) => v <<< (64 + 16 * i)
  (List.range (n + 1)).map fun t =>
    let p := par.getD t (0, 0)
    let base := es.getD t 0 ||| f p.1 0 ||| f p.2 1 ||| f (srt.getD t 0) 2 |||
      f (sri.getD t 0) 3 ||| f (w t) (4 + 2 * k)
    (List.range k).foldl (fun acc s =>
      acc ||| f (C.getD (k * t + s) 0) (4 + s) ||| f (POS.getD (k * t + s) 0) (4 + k + s)) base

meta def gM : Array Nat := ((List.finRange 12).take 9 |>.map numM).toArray

meta def oneM : Nat := 34630287489

meta def tabM : Array Nat × Array (Nat × Nat) × Array Nat × Array Nat :=
  bfsM oneM (fun x s => mulM x gM[s]!) 9 512

meta def wM (x : Nat) : Nat :=
  ((List.range 9).find? fun j => mulM x gM[j]! != mulM gM[j]! x).getD 9

meta def recM : List Nat :=
  gM.toList ++ recsM 9 tabM (fun t => wM (tabM.1.getD t 0))

end CFSG.KD.YamakiS0.Gen

#kss_ntree CFSG.KD.YamakiS0.REC CFSG.KD.YamakiS0.Gen.recM
