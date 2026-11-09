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

namespace CFSG.KD.G2Three.Gen

meta def gX : List Nat :=
  (String.splitOn (include_str "Rec.0.txt") ",").map String.toNat!

meta def xX : List Nat :=
  (String.splitOn (include_str "Rec.1.txt") ",").map String.toNat!

meta def paX : List Nat :=
  (String.splitOn (include_str "Rec.2.txt") ",").map String.toNat!

meta def pbX : List Nat :=
  (String.splitOn (include_str "Rec.3.txt") ",").map String.toNat!

meta def cX : List Nat :=
  (String.splitOn (include_str "Rec.4.txt") ",").map String.toNat!

meta def posX : List Nat :=
  (String.splitOn (include_str "Rec.5.txt") ",").map String.toNat!

meta def srtX : List Nat :=
  (String.splitOn (include_str "Rec.6.txt") ",").map String.toNat!

meta def sriX : List Nat :=
  (String.splitOn (include_str "Rec.7.txt") ",").map String.toNat!

meta def gS : List Nat :=
  (String.splitOn (include_str "Rec.8.txt") ",").map String.toNat!

meta def xS : List Nat :=
  (String.splitOn (include_str "Rec.9.txt") ",").map String.toNat!

meta def paS : List Nat :=
  (String.splitOn (include_str "Rec.10.txt") ",").map String.toNat!

meta def pbS : List Nat :=
  (String.splitOn (include_str "Rec.11.txt") ",").map String.toNat!

meta def cS : List Nat :=
  (String.splitOn (include_str "Rec.12.txt") ",").map String.toNat!

meta def posS : List Nat :=
  (String.splitOn (include_str "Rec.13.txt") ",").map String.toNat!

meta def srtS : List Nat :=
  (String.splitOn (include_str "Rec.14.txt") ",").map String.toNat!

meta def sriS : List Nat :=
  (String.splitOn (include_str "Rec.15.txt") ",").map String.toNat!

meta def gP : List Nat :=
  (String.splitOn (include_str "Rec.16.txt") ",").map String.toNat!

meta def xP : List Nat :=
  (String.splitOn (include_str "Rec.17.txt") ",").map String.toNat!

meta def paP : List Nat :=
  (String.splitOn (include_str "Rec.18.txt") ",").map String.toNat!

meta def pbP : List Nat :=
  (String.splitOn (include_str "Rec.19.txt") ",").map String.toNat!

meta def cP : List Nat :=
  (String.splitOn (include_str "Rec.20.txt") ",").map String.toNat!

meta def posP : List Nat :=
  (String.splitOn (include_str "Rec.21.txt") ",").map String.toNat!

meta def srtP : List Nat :=
  (String.splitOn (include_str "Rec.22.txt") ",").map String.toNat!

meta def sriP : List Nat :=
  (String.splitOn (include_str "Rec.23.txt") ",").map String.toNat!

meta def gA : List Nat :=
  (String.splitOn (include_str "Rec.24.txt") ",").map String.toNat!

meta def gB : List Nat :=
  (String.splitOn (include_str "Rec.25.txt") ",").map String.toNat!

meta def xO : List Nat :=
  (String.splitOn (include_str "Rec.26.txt") ",").map String.toNat!

meta def oaO : List Nat :=
  (String.splitOn (include_str "Rec.27.txt") ",").map String.toNat!

meta def obO : List Nat :=
  (String.splitOn (include_str "Rec.28.txt") ",").map String.toNat!

meta def srtO : List Nat :=
  (String.splitOn (include_str "Rec.29.txt") ",").map String.toNat!

meta def sriO : List Nat :=
  (String.splitOn (include_str "Rec.30.txt") ",").map String.toNat!

meta def idxM : List Nat :=
  (String.splitOn (include_str "Rec.31.txt") ",").map String.toNat!

end CFSG.KD.G2Three.Gen

#kss_ntree CFSG.KD.G2Three.GX CFSG.KD.G2Three.Gen.gX
#kss_ntree CFSG.KD.G2Three.XX CFSG.KD.G2Three.Gen.xX
#kss_ntree CFSG.KD.G2Three.PAX CFSG.KD.G2Three.Gen.paX
#kss_ntree CFSG.KD.G2Three.PBX CFSG.KD.G2Three.Gen.pbX
#kss_ntree CFSG.KD.G2Three.CX CFSG.KD.G2Three.Gen.cX
#kss_ntree CFSG.KD.G2Three.POSX CFSG.KD.G2Three.Gen.posX
#kss_ntree CFSG.KD.G2Three.SRTX CFSG.KD.G2Three.Gen.srtX
#kss_ntree CFSG.KD.G2Three.SRIX CFSG.KD.G2Three.Gen.sriX

#kss_ntree CFSG.KD.G2Three.GS CFSG.KD.G2Three.Gen.gS
#kss_ntree CFSG.KD.G2Three.XS CFSG.KD.G2Three.Gen.xS
#kss_ntree CFSG.KD.G2Three.PAS CFSG.KD.G2Three.Gen.paS
#kss_ntree CFSG.KD.G2Three.PBS CFSG.KD.G2Three.Gen.pbS
#kss_ntree CFSG.KD.G2Three.CS CFSG.KD.G2Three.Gen.cS
#kss_ntree CFSG.KD.G2Three.POSS CFSG.KD.G2Three.Gen.posS
#kss_ntree CFSG.KD.G2Three.SRTS CFSG.KD.G2Three.Gen.srtS
#kss_ntree CFSG.KD.G2Three.SRIS CFSG.KD.G2Three.Gen.sriS

#kss_ntree CFSG.KD.G2Three.GP CFSG.KD.G2Three.Gen.gP
#kss_ntree CFSG.KD.G2Three.XP CFSG.KD.G2Three.Gen.xP
#kss_ntree CFSG.KD.G2Three.PAP CFSG.KD.G2Three.Gen.paP
#kss_ntree CFSG.KD.G2Three.PBP CFSG.KD.G2Three.Gen.pbP
#kss_ntree CFSG.KD.G2Three.CP CFSG.KD.G2Three.Gen.cP
#kss_ntree CFSG.KD.G2Three.POSP CFSG.KD.G2Three.Gen.posP
#kss_ntree CFSG.KD.G2Three.SRTP CFSG.KD.G2Three.Gen.srtP
#kss_ntree CFSG.KD.G2Three.SRIP CFSG.KD.G2Three.Gen.sriP

#kss_ntree CFSG.KD.G2Three.GA CFSG.KD.G2Three.Gen.gA
#kss_ntree CFSG.KD.G2Three.GB CFSG.KD.G2Three.Gen.gB
#kss_ntree CFSG.KD.G2Three.XO CFSG.KD.G2Three.Gen.xO
#kss_ntree CFSG.KD.G2Three.OA CFSG.KD.G2Three.Gen.oaO
#kss_ntree CFSG.KD.G2Three.OB CFSG.KD.G2Three.Gen.obO
#kss_ntree CFSG.KD.G2Three.SRTO CFSG.KD.G2Three.Gen.srtO
#kss_ntree CFSG.KD.G2Three.SRIO CFSG.KD.G2Three.Gen.sriO
#kss_ntree CFSG.KD.G2Three.IDX CFSG.KD.G2Three.Gen.idxM
