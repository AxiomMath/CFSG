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

namespace CFSG.KD.U43P.Gen

meta def sqL : List Nat :=
  (String.splitOn (include_str "Rec.0.txt") ",").map String.toNat!

meta def kndL : List Nat :=
  (String.splitOn (include_str "Rec.1.txt") ",").map String.toNat!

meta def caL : List Nat :=
  (String.splitOn (include_str "Rec.2.txt") ",").map String.toNat!

meta def cbL : List Nat :=
  (String.splitOn (include_str "Rec.3.txt") ",").map String.toNat!

meta def olL : List Nat :=
  (String.splitOn (include_str "Rec.4.txt") ",").map String.toNat!

meta def oliL : List Nat :=
  (String.splitOn (include_str "Rec.5.txt") ",").map String.toNat!

meta def wpL : List Nat :=
  (String.splitOn (include_str "Rec.6.txt") ",").map String.toNat!

meta def wcL : List Nat :=
  (String.splitOn (include_str "Rec.7.txt") ",").map String.toNat!

meta def yrL : List Nat :=
  (String.splitOn (include_str "Rec.8.txt") ",").map String.toNat!

end CFSG.KD.U43P.Gen

#kss_ntree CFSG.KD.U43P.SQP CFSG.KD.U43P.Gen.sqL
#kss_ntree CFSG.KD.U43P.KND CFSG.KD.U43P.Gen.kndL
#kss_ntree CFSG.KD.U43P.CAP CFSG.KD.U43P.Gen.caL
#kss_ntree CFSG.KD.U43P.CBP CFSG.KD.U43P.Gen.cbL
#kss_ntree CFSG.KD.U43P.OL CFSG.KD.U43P.Gen.olL
#kss_ntree CFSG.KD.U43P.OLI CFSG.KD.U43P.Gen.oliL
#kss_ntree CFSG.KD.U43P.WP CFSG.KD.U43P.Gen.wpL
#kss_ntree CFSG.KD.U43P.WC CFSG.KD.U43P.Gen.wcL
#kss_ntree CFSG.KD.U43P.YR CFSG.KD.U43P.Gen.yrL
