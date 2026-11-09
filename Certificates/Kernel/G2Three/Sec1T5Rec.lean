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

namespace CFSG.KD.G2Three.Sec1.Gen

meta def uL : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.0.txt") ",").map String.toNat!

meta def relA : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.1.txt") ",").map String.toNat!

meta def relB : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.2.txt") ",").map String.toNat!

meta def relC : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.3.txt") ",").map String.toNat!

meta def relD : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.4.txt") ",").map String.toNat!

meta def nrelA : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.5.txt") ",").map String.toNat!

meta def nrelB : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.6.txt") ",").map String.toNat!

meta def nrelC : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.7.txt") ",").map String.toNat!

meta def nrelD : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.8.txt") ",").map String.toNat!

meta def xXL : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.9.txt") ",").map String.toNat!

meta def paX : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.10.txt") ",").map String.toNat!

meta def pbX : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.11.txt") ",").map String.toNat!

meta def posX : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.12.txt") ",").map String.toNat!

meta def srtX : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.13.txt") ",").map String.toNat!

meta def sriX : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.14.txt") ",").map String.toNat!

meta def i5 : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.15.txt") ",").map String.toNat!

meta def xSL : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.16.txt") ",").map String.toNat!

meta def paS : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.17.txt") ",").map String.toNat!

meta def pbS : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.18.txt") ",").map String.toNat!

meta def posS : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.19.txt") ",").map String.toNat!

meta def srtS : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.20.txt") ",").map String.toNat!

meta def sriS : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.21.txt") ",").map String.toNat!

meta def xAL : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.22.txt") ",").map String.toNat!

meta def paA : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.23.txt") ",").map String.toNat!

meta def pbA : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.24.txt") ",").map String.toNat!

meta def posA : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.25.txt") ",").map String.toNat!

meta def srtA : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.26.txt") ",").map String.toNat!

meta def sriA : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.27.txt") ",").map String.toNat!

meta def gB : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.28.txt") ",").map String.toNat!

meta def xBL : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.29.txt") ",").map String.toNat!

meta def paB : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.30.txt") ",").map String.toNat!

meta def pbB : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.31.txt") ",").map String.toNat!

meta def posB : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.32.txt") ",").map String.toNat!

meta def srtB : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.33.txt") ",").map String.toNat!

meta def sriB : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.34.txt") ",").map String.toNat!

meta def gP : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.35.txt") ",").map String.toNat!

meta def xPL : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.36.txt") ",").map String.toNat!

meta def paP : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.37.txt") ",").map String.toNat!

meta def pbP : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.38.txt") ",").map String.toNat!

meta def posP : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.39.txt") ",").map String.toNat!

meta def srtP : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.40.txt") ",").map String.toNat!

meta def sriP : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.41.txt") ",").map String.toNat!

meta def gC : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.42.txt") ",").map String.toNat!

meta def xCL : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.43.txt") ",").map String.toNat!

meta def paC : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.44.txt") ",").map String.toNat!

meta def pbC : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.45.txt") ",").map String.toNat!

meta def posC : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.46.txt") ",").map String.toNat!

meta def srtC : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.47.txt") ",").map String.toNat!

meta def sriC : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.48.txt") ",").map String.toNat!

meta def gJ : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.49.txt") ",").map String.toNat!

meta def xJL : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.50.txt") ",").map String.toNat!

meta def paJ : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.51.txt") ",").map String.toNat!

meta def pbJ : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.52.txt") ",").map String.toNat!

meta def posJ : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.53.txt") ",").map String.toNat!

meta def srtJ : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.54.txt") ",").map String.toNat!

meta def sriJ : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.55.txt") ",").map String.toNat!

meta def gF : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.56.txt") ",").map String.toNat!

meta def xFL : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.57.txt") ",").map String.toNat!

meta def srtF : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.58.txt") ",").map String.toNat!

meta def sriF : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.59.txt") ",").map String.toNat!

meta def gE : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.60.txt") ",").map String.toNat!

meta def xEL : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.61.txt") ",").map String.toNat!

meta def srtE : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.62.txt") ",").map String.toNat!

meta def sriE : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.63.txt") ",").map String.toNat!

meta def gY : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.64.txt") ",").map String.toNat!

meta def xYL : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.65.txt") ",").map String.toNat!

meta def srtY : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.66.txt") ",").map String.toNat!

meta def sriY : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.67.txt") ",").map String.toNat!

meta def mG : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.68.txt") ",").map String.toNat!

meta def mL : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.69.txt") ",").map String.toNat!

meta def x9L : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.70.txt") ",").map String.toNat!

meta def pa9 : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.71.txt") ",").map String.toNat!

meta def pb9 : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.72.txt") ",").map String.toNat!

meta def pos9 : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.73.txt") ",").map String.toNat!

meta def srt9 : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.74.txt") ",").map String.toNat!

meta def sri9 : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.75.txt") ",").map String.toNat!

meta def nbL : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.76.txt") ",").map String.toNat!

meta def njL : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.77.txt") ",").map String.toNat!

meta def zbL : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.78.txt") ",").map String.toNat!

meta def rjL : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.79.txt") ",").map String.toNat!

meta def rjW : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.80.txt") ",").map String.toNat!

meta def rjT : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.81.txt") ",").map String.toNat!

meta def rjZ : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.82.txt") ",").map String.toNat!

meta def raL : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.83.txt") ",").map String.toNat!

meta def raW : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.84.txt") ",").map String.toNat!

meta def raT : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.85.txt") ",").map String.toNat!

meta def raF : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.86.txt") ",").map String.toNat!

meta def p4I : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.87.txt") ",").map String.toNat!

meta def p4J : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.88.txt") ",").map String.toNat!

meta def ywL : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.89.txt") ",").map String.toNat!

meta def cewL : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.90.txt") ",").map String.toNat!

meta def ceL : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.91.txt") ",").map String.toNat!

meta def p7I : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.92.txt") ",").map String.toNat!

meta def p7J : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.93.txt") ",").map String.toNat!

meta def czL : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.94.txt") ",").map String.toNat!

meta def zcL : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.95.txt") ",").map String.toNat!

meta def bcU : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.96.txt") ",").map String.toNat!

meta def bcV : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.97.txt") ",").map String.toNat!

meta def bcL : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.98.txt") ",").map String.toNat!

meta def edI : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.99.txt") ",").map String.toNat!

meta def edJ : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.100.txt") ",").map String.toNat!

meta def edD : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.101.txt") ",").map String.toNat!

meta def edW : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.102.txt") ",").map String.toNat!

meta def iqL : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.103.txt") ",").map String.toNat!

meta def tpL : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.104.txt") ",").map String.toNat!

meta def jzL : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.105.txt") ",").map String.toNat!

meta def xs2L : List Nat :=
  (String.splitOn (include_str "Sec1T5Rec.106.txt") ",").map String.toNat!

end CFSG.KD.G2Three.Sec1.Gen

#kss_ntree CFSG.KD.G2Three.Sec1.Q5U CFSG.KD.G2Three.Sec1.Gen.uL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5RA CFSG.KD.G2Three.Sec1.Gen.relA
#kss_ntree CFSG.KD.G2Three.Sec1.Q5RB CFSG.KD.G2Three.Sec1.Gen.relB
#kss_ntree CFSG.KD.G2Three.Sec1.Q5RC CFSG.KD.G2Three.Sec1.Gen.relC
#kss_ntree CFSG.KD.G2Three.Sec1.Q5RD CFSG.KD.G2Three.Sec1.Gen.relD
#kss_ntree CFSG.KD.G2Three.Sec1.Q5NA CFSG.KD.G2Three.Sec1.Gen.nrelA
#kss_ntree CFSG.KD.G2Three.Sec1.Q5NB CFSG.KD.G2Three.Sec1.Gen.nrelB
#kss_ntree CFSG.KD.G2Three.Sec1.Q5NC CFSG.KD.G2Three.Sec1.Gen.nrelC
#kss_ntree CFSG.KD.G2Three.Sec1.Q5ND CFSG.KD.G2Three.Sec1.Gen.nrelD

#kss_ntree CFSG.KD.G2Three.Sec1.Q5X CFSG.KD.G2Three.Sec1.Gen.xXL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5XPA CFSG.KD.G2Three.Sec1.Gen.paX
#kss_ntree CFSG.KD.G2Three.Sec1.Q5XPB CFSG.KD.G2Three.Sec1.Gen.pbX
#kss_ntree CFSG.KD.G2Three.Sec1.Q5XPOS CFSG.KD.G2Three.Sec1.Gen.posX
#kss_ntree CFSG.KD.G2Three.Sec1.Q5XSRT CFSG.KD.G2Three.Sec1.Gen.srtX
#kss_ntree CFSG.KD.G2Three.Sec1.Q5XSRI CFSG.KD.G2Three.Sec1.Gen.sriX
#kss_ntree CFSG.KD.G2Three.Sec1.Q5I5 CFSG.KD.G2Three.Sec1.Gen.i5

#kss_ntree CFSG.KD.G2Three.Sec1.Q5S CFSG.KD.G2Three.Sec1.Gen.xSL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5SPA CFSG.KD.G2Three.Sec1.Gen.paS
#kss_ntree CFSG.KD.G2Three.Sec1.Q5SPB CFSG.KD.G2Three.Sec1.Gen.pbS
#kss_ntree CFSG.KD.G2Three.Sec1.Q5SPOS CFSG.KD.G2Three.Sec1.Gen.posS
#kss_ntree CFSG.KD.G2Three.Sec1.Q5SSRT CFSG.KD.G2Three.Sec1.Gen.srtS
#kss_ntree CFSG.KD.G2Three.Sec1.Q5SSRI CFSG.KD.G2Three.Sec1.Gen.sriS

#kss_ntree CFSG.KD.G2Three.Sec1.Q5A CFSG.KD.G2Three.Sec1.Gen.xAL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5APA CFSG.KD.G2Three.Sec1.Gen.paA
#kss_ntree CFSG.KD.G2Three.Sec1.Q5APB CFSG.KD.G2Three.Sec1.Gen.pbA
#kss_ntree CFSG.KD.G2Three.Sec1.Q5APOS CFSG.KD.G2Three.Sec1.Gen.posA
#kss_ntree CFSG.KD.G2Three.Sec1.Q5ASRT CFSG.KD.G2Three.Sec1.Gen.srtA
#kss_ntree CFSG.KD.G2Three.Sec1.Q5ASRI CFSG.KD.G2Three.Sec1.Gen.sriA

#kss_ntree CFSG.KD.G2Three.Sec1.Q5BG CFSG.KD.G2Three.Sec1.Gen.gB
#kss_ntree CFSG.KD.G2Three.Sec1.Q5B CFSG.KD.G2Three.Sec1.Gen.xBL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5BPA CFSG.KD.G2Three.Sec1.Gen.paB
#kss_ntree CFSG.KD.G2Three.Sec1.Q5BPB CFSG.KD.G2Three.Sec1.Gen.pbB
#kss_ntree CFSG.KD.G2Three.Sec1.Q5BPOS CFSG.KD.G2Three.Sec1.Gen.posB
#kss_ntree CFSG.KD.G2Three.Sec1.Q5BSRT CFSG.KD.G2Three.Sec1.Gen.srtB
#kss_ntree CFSG.KD.G2Three.Sec1.Q5BSRI CFSG.KD.G2Three.Sec1.Gen.sriB

#kss_ntree CFSG.KD.G2Three.Sec1.Q5PG CFSG.KD.G2Three.Sec1.Gen.gP
#kss_ntree CFSG.KD.G2Three.Sec1.Q5P CFSG.KD.G2Three.Sec1.Gen.xPL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5PPA CFSG.KD.G2Three.Sec1.Gen.paP
#kss_ntree CFSG.KD.G2Three.Sec1.Q5PPB CFSG.KD.G2Three.Sec1.Gen.pbP
#kss_ntree CFSG.KD.G2Three.Sec1.Q5PPOS CFSG.KD.G2Three.Sec1.Gen.posP
#kss_ntree CFSG.KD.G2Three.Sec1.Q5PSRT CFSG.KD.G2Three.Sec1.Gen.srtP
#kss_ntree CFSG.KD.G2Three.Sec1.Q5PSRI CFSG.KD.G2Three.Sec1.Gen.sriP

#kss_ntree CFSG.KD.G2Three.Sec1.Q5CG CFSG.KD.G2Three.Sec1.Gen.gC
#kss_ntree CFSG.KD.G2Three.Sec1.Q5C CFSG.KD.G2Three.Sec1.Gen.xCL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5CPA CFSG.KD.G2Three.Sec1.Gen.paC
#kss_ntree CFSG.KD.G2Three.Sec1.Q5CPB CFSG.KD.G2Three.Sec1.Gen.pbC
#kss_ntree CFSG.KD.G2Three.Sec1.Q5CPOS CFSG.KD.G2Three.Sec1.Gen.posC
#kss_ntree CFSG.KD.G2Three.Sec1.Q5CSRT CFSG.KD.G2Three.Sec1.Gen.srtC
#kss_ntree CFSG.KD.G2Three.Sec1.Q5CSRI CFSG.KD.G2Three.Sec1.Gen.sriC

#kss_ntree CFSG.KD.G2Three.Sec1.Q5JG CFSG.KD.G2Three.Sec1.Gen.gJ
#kss_ntree CFSG.KD.G2Three.Sec1.Q5J CFSG.KD.G2Three.Sec1.Gen.xJL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5JPA CFSG.KD.G2Three.Sec1.Gen.paJ
#kss_ntree CFSG.KD.G2Three.Sec1.Q5JPB CFSG.KD.G2Three.Sec1.Gen.pbJ
#kss_ntree CFSG.KD.G2Three.Sec1.Q5JPOS CFSG.KD.G2Three.Sec1.Gen.posJ
#kss_ntree CFSG.KD.G2Three.Sec1.Q5JSRT CFSG.KD.G2Three.Sec1.Gen.srtJ
#kss_ntree CFSG.KD.G2Three.Sec1.Q5JSRI CFSG.KD.G2Three.Sec1.Gen.sriJ

#kss_ntree CFSG.KD.G2Three.Sec1.Q5FG CFSG.KD.G2Three.Sec1.Gen.gF
#kss_ntree CFSG.KD.G2Three.Sec1.Q5F CFSG.KD.G2Three.Sec1.Gen.xFL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5FSRT CFSG.KD.G2Three.Sec1.Gen.srtF
#kss_ntree CFSG.KD.G2Three.Sec1.Q5FSRI CFSG.KD.G2Three.Sec1.Gen.sriF
#kss_ntree CFSG.KD.G2Three.Sec1.Q5EG CFSG.KD.G2Three.Sec1.Gen.gE
#kss_ntree CFSG.KD.G2Three.Sec1.Q5E CFSG.KD.G2Three.Sec1.Gen.xEL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5ESRT CFSG.KD.G2Three.Sec1.Gen.srtE
#kss_ntree CFSG.KD.G2Three.Sec1.Q5ESRI CFSG.KD.G2Three.Sec1.Gen.sriE
#kss_ntree CFSG.KD.G2Three.Sec1.Q5YG CFSG.KD.G2Three.Sec1.Gen.gY
#kss_ntree CFSG.KD.G2Three.Sec1.Q5Y CFSG.KD.G2Three.Sec1.Gen.xYL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5YSRT CFSG.KD.G2Three.Sec1.Gen.srtY
#kss_ntree CFSG.KD.G2Three.Sec1.Q5YSRI CFSG.KD.G2Three.Sec1.Gen.sriY

#kss_ntree CFSG.KD.G2Three.Sec1.Q5MG CFSG.KD.G2Three.Sec1.Gen.mG
#kss_ntree CFSG.KD.G2Three.Sec1.Q5M CFSG.KD.G2Three.Sec1.Gen.mL
#kss_ntree CFSG.KD.G2Three.Sec1.Q59 CFSG.KD.G2Three.Sec1.Gen.x9L
#kss_ntree CFSG.KD.G2Three.Sec1.Q59PA CFSG.KD.G2Three.Sec1.Gen.pa9
#kss_ntree CFSG.KD.G2Three.Sec1.Q59PB CFSG.KD.G2Three.Sec1.Gen.pb9
#kss_ntree CFSG.KD.G2Three.Sec1.Q59POS CFSG.KD.G2Three.Sec1.Gen.pos9
#kss_ntree CFSG.KD.G2Three.Sec1.Q59SRT CFSG.KD.G2Three.Sec1.Gen.srt9
#kss_ntree CFSG.KD.G2Three.Sec1.Q59SRI CFSG.KD.G2Three.Sec1.Gen.sri9

#kss_ntree CFSG.KD.G2Three.Sec1.Q5NBW CFSG.KD.G2Three.Sec1.Gen.nbL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5NJW CFSG.KD.G2Three.Sec1.Gen.njL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5ZB CFSG.KD.G2Three.Sec1.Gen.zbL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5RJ CFSG.KD.G2Three.Sec1.Gen.rjL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5RJW CFSG.KD.G2Three.Sec1.Gen.rjW
#kss_ntree CFSG.KD.G2Three.Sec1.Q5RJT CFSG.KD.G2Three.Sec1.Gen.rjT
#kss_ntree CFSG.KD.G2Three.Sec1.Q5RJZ CFSG.KD.G2Three.Sec1.Gen.rjZ
#kss_ntree CFSG.KD.G2Three.Sec1.Q5RAR CFSG.KD.G2Three.Sec1.Gen.raL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5RAW CFSG.KD.G2Three.Sec1.Gen.raW
#kss_ntree CFSG.KD.G2Three.Sec1.Q5RAT CFSG.KD.G2Three.Sec1.Gen.raT
#kss_ntree CFSG.KD.G2Three.Sec1.Q5RAF CFSG.KD.G2Three.Sec1.Gen.raF
#kss_ntree CFSG.KD.G2Three.Sec1.Q5P4I CFSG.KD.G2Three.Sec1.Gen.p4I
#kss_ntree CFSG.KD.G2Three.Sec1.Q5P4J CFSG.KD.G2Three.Sec1.Gen.p4J
#kss_ntree CFSG.KD.G2Three.Sec1.Q5YW CFSG.KD.G2Three.Sec1.Gen.ywL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5CEW CFSG.KD.G2Three.Sec1.Gen.cewL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5CE CFSG.KD.G2Three.Sec1.Gen.ceL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5P7I CFSG.KD.G2Three.Sec1.Gen.p7I
#kss_ntree CFSG.KD.G2Three.Sec1.Q5P7J CFSG.KD.G2Three.Sec1.Gen.p7J
#kss_ntree CFSG.KD.G2Three.Sec1.Q5CZ CFSG.KD.G2Three.Sec1.Gen.czL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5CZW CFSG.KD.G2Three.Sec1.Gen.zcL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5CBU CFSG.KD.G2Three.Sec1.Gen.bcU
#kss_ntree CFSG.KD.G2Three.Sec1.Q5CBV CFSG.KD.G2Three.Sec1.Gen.bcV
#kss_ntree CFSG.KD.G2Three.Sec1.Q5CBW CFSG.KD.G2Three.Sec1.Gen.bcL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5EDI CFSG.KD.G2Three.Sec1.Gen.edI
#kss_ntree CFSG.KD.G2Three.Sec1.Q5EDJ CFSG.KD.G2Three.Sec1.Gen.edJ
#kss_ntree CFSG.KD.G2Three.Sec1.Q5EDD CFSG.KD.G2Three.Sec1.Gen.edD
#kss_ntree CFSG.KD.G2Three.Sec1.Q5EDW CFSG.KD.G2Three.Sec1.Gen.edW
#kss_ntree CFSG.KD.G2Three.Sec1.Q5IQ CFSG.KD.G2Three.Sec1.Gen.iqL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5TP CFSG.KD.G2Three.Sec1.Gen.tpL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5JZ CFSG.KD.G2Three.Sec1.Gen.jzL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5XS2 CFSG.KD.G2Three.Sec1.Gen.xs2L
