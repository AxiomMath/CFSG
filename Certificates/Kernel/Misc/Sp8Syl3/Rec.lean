module

public meta import Lean
meta import Certificates.Data.RudvalisFF81Sp8Torus
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

namespace CFSG.KD.Sp8Syl3.Gen

open CFSG.RankThree.PartTwo.Sec21.FF81.Sp8

meta def c64 (x : List Nat) : Nat := x.foldr (fun c acc => c + 256 * acc) 0

meta def mulM (A B : Nat) : Nat := Id.run do
  let mut r := 0
  for j in [0:8] do
    let b := (B >>> (8 * j)) &&& 255
    let mut col := 0
    for i in [0:8] do
      if (b >>> i) &&& 1 == 1 then
        col := col ^^^ ((A >>> (8 * i)) &&& 255)
    r := r ||| (col <<< (8 * j))
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

meta def gM : Array Nat := (pGens.map c64).toArray
meta def ccM : Array Nat := (conjL.map c64).toArray
meta def ciM : Array Nat := (conjL.map fun c => c64 (invS c)).toArray
meta def oneM : Nat := c64 CFSG.Quasithin.H13.Mat8Cert.one8

meta def tabE : Array Nat × Array (Nat × Nat) × Array Nat × Array Nat :=
  bfsM oneM (fun x s => mulM x gM[s]!) 4 81

meta def tabP : Array Nat × Array (Nat × Nat) × Array Nat × Array Nat :=
  bfsM oneM (fun x s => mulM x gM[s]!) 5 243

meta def wM (p : Nat) : Nat :=
  let E := tabE.1
  match E.findIdx? (· == p) with
  | some e => e
  | none =>
    let r := (List.range 3).findSome? fun c =>
      let y := mulM (mulM ccM[c]! p) ciM[c]!
      (E.findIdx? (· == y)).map fun e => 81 + 81 * c + e
    r.getD 65535

meta def recM : List Nat :=
  gM.toList ++ ccM.toList ++ ciM.toList ++ recsM 4 tabE (fun _ => 0) ++
    recsM 5 tabP (fun t => wM (tabP.1.getD t 0))

end CFSG.KD.Sp8Syl3.Gen

#kss_ntree CFSG.KD.Sp8Syl3.REC CFSG.KD.Sp8Syl3.Gen.recM
