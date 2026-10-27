module

public meta import Lean
meta import CFSG.RankThree.PartTwo.Census.Carrier.Sp6TwoData
meta import Certificates.Data.Sp62.Involutions
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

namespace CFSG.KD.Sp62X1.Gen

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.H13.U3

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

meta def recsM (k : Nat) (b : Array Nat × Array (Nat × Nat) × Array Nat × Array Nat) :
    List Nat :=
  let (es, par, C, POS) := b
  let (srt, sri) := sortM es
  let n := es.size
  let f := fun (v : Nat) (i : Nat) => v <<< (40 + 16 * i)
  (List.range (n + 1)).map fun t =>
    let p := par.getD t (0, 0)
    let base := es.getD t 0 ||| f p.1 0 ||| f p.2 1 ||| f (srt.getD t 0) 2 ||| f (sri.getD t 0) 3
    (List.range k).foldl (fun acc s =>
      acc ||| f (C.getD (k * t + s) 0) (4 + s) ||| f (POS.getD (k * t + s) 0) (4 + k + s)) base

meta def sylM : Array Nat :=
  let g := (sylowP.map fun cc => pkM cc.1).toArray
  (bfsM (pkM one6) (fun x s => mulM x g[s]!) g.size 24000).1

meta def gaM : Array Nat := #[pkM aC, pkM bC]
meta def gbM : Array Nat := #[pkM aI, pkM bI]

meta def orbM (t : List Nat) : Array Nat :=
  (bfsM (pkM t) (fun x s => mulM (mulM gaM[s]! x) gbM[s]!) 2 4000).1

meta def idxM (es : Array Nat) (x : Nat) : Nat := (es.findIdx? (· == x)).getD 0

meta def genM : Array Nat := (sp62AC.map pkM).toArray

meta def recM : List Nat :=
  genM.toList ++ genM.toList.map (idxM sylM) ++
    [idxM (orbM t0C) (pkM sp62Y0), idxM (orbM t1C) (pkM sp62Y1), idxM (orbM t2C) (pkM sp62Y2),
      idxM (orbM t3C) (pkM sp62Y3)] ++
    recsM 6 (bfsM (pkM one6) (fun x s => mulM x genM[s]!) 6 24000)

end CFSG.KD.Sp62X1.Gen

#kss_ntree CFSG.KD.Sp62X1.XR CFSG.KD.Sp62X1.Gen.recM
