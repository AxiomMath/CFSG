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

namespace CFSG.KD.G2Three.Sec1.Gen2

meta def gB : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec2.0.txt") ",").map String.toNat!

meta def xBL : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec2.1.txt") ",").map String.toNat!

meta def paB : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec2.2.txt") ",").map String.toNat!

meta def pbB : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec2.3.txt") ",").map String.toNat!

meta def posB : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec2.4.txt") ",").map String.toNat!

meta def srtB : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec2.5.txt") ",").map String.toNat!

meta def sriB : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec2.6.txt") ",").map String.toNat!

meta def scC : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec2.7.txt") ",").map String.toNat!

meta def scD : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec2.8.txt") ",").map String.toNat!

meta def scW : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec2.9.txt") ",").map String.toNat!

meta def bcC : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec2.10.txt") ",").map String.toNat!

meta def bcD : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec2.11.txt") ",").map String.toNat!

meta def bcW : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec2.12.txt") ",").map String.toNat!

end CFSG.KD.G2Three.Sec1.Gen2

#kss_ntree CFSG.KD.G2Three.Sec1.R1BG CFSG.KD.G2Three.Sec1.Gen2.gB
#kss_ntree CFSG.KD.G2Three.Sec1.R1B CFSG.KD.G2Three.Sec1.Gen2.xBL
#kss_ntree CFSG.KD.G2Three.Sec1.R1BPA CFSG.KD.G2Three.Sec1.Gen2.paB
#kss_ntree CFSG.KD.G2Three.Sec1.R1BPB CFSG.KD.G2Three.Sec1.Gen2.pbB
#kss_ntree CFSG.KD.G2Three.Sec1.R1BPOS CFSG.KD.G2Three.Sec1.Gen2.posB
#kss_ntree CFSG.KD.G2Three.Sec1.R1BSRT CFSG.KD.G2Three.Sec1.Gen2.srtB
#kss_ntree CFSG.KD.G2Three.Sec1.R1BSRI CFSG.KD.G2Three.Sec1.Gen2.sriB
#kss_ntree CFSG.KD.G2Three.Sec1.R1SC CFSG.KD.G2Three.Sec1.Gen2.scC
#kss_ntree CFSG.KD.G2Three.Sec1.R1SD CFSG.KD.G2Three.Sec1.Gen2.scD
#kss_ntree CFSG.KD.G2Three.Sec1.R1SW CFSG.KD.G2Three.Sec1.Gen2.scW
#kss_ntree CFSG.KD.G2Three.Sec1.R1BC CFSG.KD.G2Three.Sec1.Gen2.bcC
#kss_ntree CFSG.KD.G2Three.Sec1.R1BD CFSG.KD.G2Three.Sec1.Gen2.bcD
#kss_ntree CFSG.KD.G2Three.Sec1.R1BW CFSG.KD.G2Three.Sec1.Gen2.bcW
