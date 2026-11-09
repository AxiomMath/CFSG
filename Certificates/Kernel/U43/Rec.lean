module

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

namespace CFSG.KD.U43.Gen

meta def aL : List Nat :=
  (String.splitOn (include_str "Rec.0.txt") ",").map String.toNat!

meta def gL : List Nat :=
  (String.splitOn (include_str "Rec.1.txt") ",").map String.toNat!

meta def xL : List Nat :=
  (String.splitOn (include_str "Rec.2.txt") ",").map String.toNat!

meta def posL : List Nat :=
  (String.splitOn (include_str "Rec.3.txt") ",").map String.toNat!

meta def srtL : List Nat :=
  (String.splitOn (include_str "Rec.4.txt") ",").map String.toNat!

meta def sriL : List Nat :=
  (String.splitOn (include_str "Rec.5.txt") ",").map String.toNat!

meta def kwL : List Nat :=
  (String.splitOn (include_str "Rec.6.txt") ",").map String.toNat!

end CFSG.KD.U43.Gen

#kss_ntree CFSG.KD.U43.UA CFSG.KD.U43.Gen.aL
#kss_ntree CFSG.KD.U43.UG CFSG.KD.U43.Gen.gL
#kss_ntree CFSG.KD.U43.UX CFSG.KD.U43.Gen.xL
#kss_ntree CFSG.KD.U43.UPOS CFSG.KD.U43.Gen.posL
#kss_ntree CFSG.KD.U43.USRT CFSG.KD.U43.Gen.srtL
#kss_ntree CFSG.KD.U43.USRI CFSG.KD.U43.Gen.sriL
#kss_ntree CFSG.KD.U43.UKW CFSG.KD.U43.Gen.kwL
