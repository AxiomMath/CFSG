module

public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Data.Kernel.G2Three.Sec1F
public import Certificates.Kernel.G2Three.Sec1T5Rec
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

namespace CFSG.KD.G2Three.Sec1T3.Gen

meta def xL : List Nat :=
  (String.splitOn (include_str "Sec1T3Rec.0.txt") ",").map String.toNat!

meta def srtL : List Nat :=
  (String.splitOn (include_str "Sec1T3Rec.1.txt") ",").map String.toNat!

meta def sriL : List Nat :=
  (String.splitOn (include_str "Sec1T3Rec.2.txt") ",").map String.toNat!

end CFSG.KD.G2Three.Sec1T3.Gen

#kss_ntree CFSG.KD.G2Three.Sec1T3.X3 CFSG.KD.G2Three.Sec1T3.Gen.xL
#kss_ntree CFSG.KD.G2Three.Sec1T3.X3SRT CFSG.KD.G2Three.Sec1T3.Gen.srtL
#kss_ntree CFSG.KD.G2Three.Sec1T3.X3SRI CFSG.KD.G2Three.Sec1T3.Gen.sriL

public section

namespace CFSG.KD.G2Three.Sec1T3

open CFSG.KD.G2Three.Sec1

@[expose] noncomputable def gS3 (s : Nat) : Nat := nIf(Nat.blt s 5, Q5U s, SIGF)

end CFSG.KD.G2Three.Sec1T3

end
