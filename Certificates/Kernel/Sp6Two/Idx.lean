module

public meta import Lean
meta import CFSG.RankThree.PartTwo.Census.Carrier.Sp6TwoData
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
meta import Mathlib
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

namespace CFSG.KD.Sp6Two.GenI

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

meta def pkI (m : List Nat) : Nat := m.foldr (fun e acc => e + 2 * acc) 0

meta def mulI (A B : Nat) : Nat := Id.run do
  let mut r := 0
  for i in [0:6] do
    let a := (A >>> (6 * i)) &&& 63
    let mut row := 0
    for k in [0:6] do
      if (a >>> k) &&& 1 == 1 then
        row := row ^^^ ((B >>> (6 * k)) &&& 63)
    r := r ||| (row <<< (6 * i))
  return r

meta def bfsI (start : Nat) (st : Nat → Nat → Nat) (k fuel : Nat) : Array Nat := Id.run do
  let mut es : Array Nat := #[start]
  let mut idx : Std.HashSet Nat := ({} : Std.HashSet Nat).insert start
  for h in [0:fuel] do
    if h < es.size then
      for s in [0:k] do
        let y := st es[h]! s
        if !idx.contains y then
          idx := idx.insert y
          es := es.push y
  return es

meta def gaI : Array Nat := #[pkI aC, pkI bC]
meta def gbI : Array Nat := #[pkI aI, pkI bI]

meta def orbIdx : Std.HashMap Nat Nat :=
  [t0C, t1C, t2C, t3C].foldl (fun m t =>
    let es := bfsI (pkI t) (fun x s => mulI (mulI gaI[s]! x) gbI[s]!) 2 4000
    (List.range es.size).foldl (fun m i => m.insert es[i]! i) m) {}

meta def idxM : List Nat :=
  let g := (sylowP.map fun cc => pkI cc.1).toArray
  let one := pkI one6
  let es := bfsI one (fun x s => mulI x g[s]!) g.size 24000
  es.toList.map fun x => if mulI x x == one && x != one then orbIdx.getD x 0 else 0

end CFSG.KD.Sp6Two.GenI

#kss_ntree CFSG.KD.Sp6Two.IDX CFSG.KD.Sp6Two.GenI.idxM
