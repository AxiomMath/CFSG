module

public meta import Lean
meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KS228Sp62.Data
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

namespace CFSG.KD.Sp62.Gen12646

open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS228Sp62 CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

meta def pkM (m : List Nat) : Nat := m.foldr (fun e acc => e + 2 * acc) 0

meta def mulM (A B : Nat) : Nat := Id.run do
  let mut r := 0
  for i in [0:6] do
    let a := (A >>> (6 * i)) &&& 63
    let mut row := 0
    for k in [0:6] do
      if (a >>> k) &&& 1 == 1 then
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

meta def recsM (b : Array Nat × Array (Nat × Nat) × Array Nat × Array Nat) (w : Nat → Nat) :
    List Nat :=
  let (es, par, C, POS) := b
  let (srt, sri) := sortM es
  let n := es.size
  let f := fun (v : Nat) (i : Nat) => v <<< (40 + 16 * i)
  (List.range (n + 1)).map fun t =>
    let p := par.getD t (0, 0)
    es.getD t 0 ||| f p.1 0 ||| f p.2 1 ||| f (srt.getD t 0) 2 ||| f (sri.getD t 0) 3 |||
      f (C.getD (2 * t) 0) 4 ||| f (C.getD (2 * t + 1) 0) 5 ||| f (POS.getD (2 * t) 0) 6 |||
      f (POS.getD (2 * t + 1) 0) 7 ||| f (w (es.getD t 0)) 8

meta def gensM (l : List (List ℕ × List ℕ)) : Array Nat := (l.map fun cc => pkM cc.1).toArray
meta def gaM : Array Nat := #[pkM aC, pkM bC]
meta def gbM : Array Nat := #[pkM aI, pkM bI]
meta def k0M : Nat := pkM k0C
meta def x0M : Nat := pkM x0C

meta def closM (l : List (List ℕ × List ℕ)) :
    Array Nat × Array (Nat × Nat) × Array Nat × Array Nat :=
  let g := gensM l
  bfsM (pkM one6) (fun x s => mulM x g[s]!) 2 24000

meta def orbM (t fuel : Nat) : List Nat :=
  recsM (bfsM t (fun x s => mulM (mulM gaM[s]! x) gbM[s]!) 2 fuel) fun _ => 0

meta def kPowM : List Nat :=
  [k0M, mulM k0M k0M, mulM k0M (mulM k0M k0M), mulM k0M (mulM k0M (mulM k0M k0M))]

meta def wM (tn : Array Nat) (y : Nat) : Nat :=
  if kPowM.any (fun p => mulM y k0M == mulM p y) then (tn.findIdx? (· == y)).getD 0 else 0

meta def headM : List Nat :=
  (gensM gkP).toList ++ (gensM gxP).toList ++ (gensM gnP).toList ++ gaM.toList ++ gbM.toList ++
    [k0M, x0M] ++ kPowM ++ [mulM x0M x0M]

meta def recM : List Nat :=
  let tn := (closM gnP).1
  headM ++ recsM (closM gkP) (fun _ => 0) ++ recsM (closM gxP) (wM tn) ++
    recsM (closM gnP) (fun _ => 0) ++ orbM x0M 1000 ++ orbM k0M 60000

end CFSG.KD.Sp62.Gen12646

#kss_ntree CFSG.KD.Sp62.R12646 CFSG.KD.Sp62.Gen12646.recM
