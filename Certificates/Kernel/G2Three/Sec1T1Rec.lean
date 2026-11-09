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

namespace CFSG.KD.G2Three.Sec1.Gen1

meta def uL : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.0.txt") ",").map String.toNat!

meta def relA : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.1.txt") ",").map String.toNat!

meta def relB : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.2.txt") ",").map String.toNat!

meta def relC : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.3.txt") ",").map String.toNat!

meta def relD : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.4.txt") ",").map String.toNat!

meta def nrelA : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.5.txt") ",").map String.toNat!

meta def nrelB : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.6.txt") ",").map String.toNat!

meta def nrelC : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.7.txt") ",").map String.toNat!

meta def nrelD : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.8.txt") ",").map String.toNat!

meta def swA : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.9.txt") ",").map String.toNat!

meta def swB : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.10.txt") ",").map String.toNat!

meta def gH : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.11.txt") ",").map String.toNat!

meta def xHL : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.12.txt") ",").map String.toNat!

meta def paH : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.13.txt") ",").map String.toNat!

meta def pbH : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.14.txt") ",").map String.toNat!

meta def posH : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.15.txt") ",").map String.toNat!

meta def srtH : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.16.txt") ",").map String.toNat!

meta def sriH : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.17.txt") ",").map String.toNat!

meta def iH : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.18.txt") ",").map String.toNat!

meta def iSW : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.19.txt") ",").map String.toNat!

meta def gK1 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.20.txt") ",").map String.toNat!

meta def xK1L : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.21.txt") ",").map String.toNat!

meta def paK1 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.22.txt") ",").map String.toNat!

meta def pbK1 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.23.txt") ",").map String.toNat!

meta def posK1 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.24.txt") ",").map String.toNat!

meta def srtK1 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.25.txt") ",").map String.toNat!

meta def sriK1 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.26.txt") ",").map String.toNat!

meta def gK2 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.27.txt") ",").map String.toNat!

meta def xK2L : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.28.txt") ",").map String.toNat!

meta def paK2 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.29.txt") ",").map String.toNat!

meta def pbK2 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.30.txt") ",").map String.toNat!

meta def posK2 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.31.txt") ",").map String.toNat!

meta def srtK2 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.32.txt") ",").map String.toNat!

meta def sriK2 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.33.txt") ",").map String.toNat!

meta def gQ1 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.34.txt") ",").map String.toNat!

meta def xQ1L : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.35.txt") ",").map String.toNat!

meta def paQ1 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.36.txt") ",").map String.toNat!

meta def pbQ1 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.37.txt") ",").map String.toNat!

meta def posQ1 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.38.txt") ",").map String.toNat!

meta def srtQ1 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.39.txt") ",").map String.toNat!

meta def sriQ1 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.40.txt") ",").map String.toNat!

meta def gQ2 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.41.txt") ",").map String.toNat!

meta def xQ2L : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.42.txt") ",").map String.toNat!

meta def paQ2 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.43.txt") ",").map String.toNat!

meta def pbQ2 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.44.txt") ",").map String.toNat!

meta def posQ2 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.45.txt") ",").map String.toNat!

meta def srtQ2 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.46.txt") ",").map String.toNat!

meta def sriQ2 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.47.txt") ",").map String.toNat!

meta def gS : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.48.txt") ",").map String.toNat!

meta def xSL : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.49.txt") ",").map String.toNat!

meta def paS : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.50.txt") ",").map String.toNat!

meta def pbS : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.51.txt") ",").map String.toNat!

meta def posS : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.52.txt") ",").map String.toNat!

meta def srtS : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.53.txt") ",").map String.toNat!

meta def sriS : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.54.txt") ",").map String.toNat!

meta def gA : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.55.txt") ",").map String.toNat!

meta def xAL : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.56.txt") ",").map String.toNat!

meta def paA : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.57.txt") ",").map String.toNat!

meta def pbA : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.58.txt") ",").map String.toNat!

meta def posA : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.59.txt") ",").map String.toNat!

meta def srtA : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.60.txt") ",").map String.toNat!

meta def sriA : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.61.txt") ",").map String.toNat!

meta def gM : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.62.txt") ",").map String.toNat!

meta def xML : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.63.txt") ",").map String.toNat!

meta def paM : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.64.txt") ",").map String.toNat!

meta def pbM : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.65.txt") ",").map String.toNat!

meta def posM : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.66.txt") ",").map String.toNat!

meta def srtM : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.67.txt") ",").map String.toNat!

meta def sriM : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.68.txt") ",").map String.toNat!

meta def iM : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.69.txt") ",").map String.toNat!

meta def iMU : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.70.txt") ",").map String.toNat!

meta def gEF : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.71.txt") ",").map String.toNat!

meta def kG : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.72.txt") ",").map String.toNat!

meta def gE : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.73.txt") ",").map String.toNat!

meta def xEL : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.74.txt") ",").map String.toNat!

meta def srtE : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.75.txt") ",").map String.toNat!

meta def sriE : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.76.txt") ",").map String.toNat!

meta def gF : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.77.txt") ",").map String.toNat!

meta def xFL : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.78.txt") ",").map String.toNat!

meta def srtF : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.79.txt") ",").map String.toNat!

meta def sriF : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.80.txt") ",").map String.toNat!

meta def gY2 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.81.txt") ",").map String.toNat!

meta def xY2L : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.82.txt") ",").map String.toNat!

meta def srtY2 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.83.txt") ",").map String.toNat!

meta def sriY2 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.84.txt") ",").map String.toNat!

meta def gY3 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.85.txt") ",").map String.toNat!

meta def xY3L : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.86.txt") ",").map String.toNat!

meta def srtY3 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.87.txt") ",").map String.toNat!

meta def sriY3 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.88.txt") ",").map String.toNat!

meta def y2W : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.89.txt") ",").map String.toNat!

meta def y3W : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.90.txt") ",").map String.toNat!

meta def kYL : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.91.txt") ",").map String.toNat!

meta def srtKY : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.92.txt") ",").map String.toNat!

meta def sriKY : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.93.txt") ",").map String.toNat!

meta def pYL : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.94.txt") ",").map String.toNat!

meta def pGL : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.95.txt") ",").map String.toNat!

meta def pUL : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.96.txt") ",").map String.toNat!

meta def xPIL : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.97.txt") ",").map String.toNat!

meta def paPI : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.98.txt") ",").map String.toNat!

meta def pbPI : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.99.txt") ",").map String.toNat!

meta def posPI : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.100.txt") ",").map String.toNat!

meta def srtPI : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.101.txt") ",").map String.toNat!

meta def sriPI : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.102.txt") ",").map String.toNat!

meta def mG : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.103.txt") ",").map String.toNat!

meta def mL : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.104.txt") ",").map String.toNat!

meta def nK1 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.105.txt") ",").map String.toNat!

meta def nK2 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.106.txt") ",").map String.toNat!

meta def nQ1 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.107.txt") ",").map String.toNat!

meta def nQ2 : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.108.txt") ",").map String.toNat!

meta def nA : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.109.txt") ",").map String.toNat!

meta def o1W : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.110.txt") ",").map String.toNat!

meta def o1K : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.111.txt") ",").map String.toNat!

meta def o1V : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.112.txt") ",").map String.toNat!

meta def o1E : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.113.txt") ",").map String.toNat!

meta def o2W : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.114.txt") ",").map String.toNat!

meta def o2K : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.115.txt") ",").map String.toNat!

meta def o2V : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.116.txt") ",").map String.toNat!

meta def o2E : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.117.txt") ",").map String.toNat!

meta def o3W : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.118.txt") ",").map String.toNat!

meta def o3K : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.119.txt") ",").map String.toNat!

meta def o3V : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.120.txt") ",").map String.toNat!

meta def o3E : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.121.txt") ",").map String.toNat!

meta def raL : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.122.txt") ",").map String.toNat!

meta def raW : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.123.txt") ",").map String.toNat!

meta def raT : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.124.txt") ",").map String.toNat!

meta def raE : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.125.txt") ",").map String.toNat!

meta def p4I : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.126.txt") ",").map String.toNat!

meta def p4J : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.127.txt") ",").map String.toNat!

meta def eo : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.128.txt") ",").map String.toNat!

meta def etU : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.129.txt") ",").map String.toNat!

meta def etV : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.130.txt") ",").map String.toNat!

meta def etK : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.131.txt") ",").map String.toNat!

meta def fxK : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.132.txt") ",").map String.toNat!

meta def ceL : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.133.txt") ",").map String.toNat!

meta def edI : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.134.txt") ",").map String.toNat!

meta def edJ : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.135.txt") ",").map String.toNat!

meta def edD : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.136.txt") ",").map String.toNat!

meta def edW : List Nat :=
  (String.splitOn (include_str "Sec1T1Rec.137.txt") ",").map String.toNat!

end CFSG.KD.G2Three.Sec1.Gen1

#kss_ntree CFSG.KD.G2Three.Sec1.R1U CFSG.KD.G2Three.Sec1.Gen1.uL
#kss_ntree CFSG.KD.G2Three.Sec1.R1RA CFSG.KD.G2Three.Sec1.Gen1.relA
#kss_ntree CFSG.KD.G2Three.Sec1.R1RB CFSG.KD.G2Three.Sec1.Gen1.relB
#kss_ntree CFSG.KD.G2Three.Sec1.R1RC CFSG.KD.G2Three.Sec1.Gen1.relC
#kss_ntree CFSG.KD.G2Three.Sec1.R1RD CFSG.KD.G2Three.Sec1.Gen1.relD
#kss_ntree CFSG.KD.G2Three.Sec1.R1NA CFSG.KD.G2Three.Sec1.Gen1.nrelA
#kss_ntree CFSG.KD.G2Three.Sec1.R1NB CFSG.KD.G2Three.Sec1.Gen1.nrelB
#kss_ntree CFSG.KD.G2Three.Sec1.R1NC CFSG.KD.G2Three.Sec1.Gen1.nrelC
#kss_ntree CFSG.KD.G2Three.Sec1.R1ND CFSG.KD.G2Three.Sec1.Gen1.nrelD
#kss_ntree CFSG.KD.G2Three.Sec1.R1SWA CFSG.KD.G2Three.Sec1.Gen1.swA
#kss_ntree CFSG.KD.G2Three.Sec1.R1SWB CFSG.KD.G2Three.Sec1.Gen1.swB

#kss_ntree CFSG.KD.G2Three.Sec1.R1HG CFSG.KD.G2Three.Sec1.Gen1.gH
#kss_ntree CFSG.KD.G2Three.Sec1.R1H CFSG.KD.G2Three.Sec1.Gen1.xHL
#kss_ntree CFSG.KD.G2Three.Sec1.R1HPA CFSG.KD.G2Three.Sec1.Gen1.paH
#kss_ntree CFSG.KD.G2Three.Sec1.R1HPB CFSG.KD.G2Three.Sec1.Gen1.pbH
#kss_ntree CFSG.KD.G2Three.Sec1.R1HPOS CFSG.KD.G2Three.Sec1.Gen1.posH
#kss_ntree CFSG.KD.G2Three.Sec1.R1HSRT CFSG.KD.G2Three.Sec1.Gen1.srtH
#kss_ntree CFSG.KD.G2Three.Sec1.R1HSRI CFSG.KD.G2Three.Sec1.Gen1.sriH
#kss_ntree CFSG.KD.G2Three.Sec1.R1IH CFSG.KD.G2Three.Sec1.Gen1.iH
#kss_ntree CFSG.KD.G2Three.Sec1.R1ISW CFSG.KD.G2Three.Sec1.Gen1.iSW

#kss_ntree CFSG.KD.G2Three.Sec1.R1K1G CFSG.KD.G2Three.Sec1.Gen1.gK1
#kss_ntree CFSG.KD.G2Three.Sec1.R1K1 CFSG.KD.G2Three.Sec1.Gen1.xK1L
#kss_ntree CFSG.KD.G2Three.Sec1.R1K1PA CFSG.KD.G2Three.Sec1.Gen1.paK1
#kss_ntree CFSG.KD.G2Three.Sec1.R1K1PB CFSG.KD.G2Three.Sec1.Gen1.pbK1
#kss_ntree CFSG.KD.G2Three.Sec1.R1K1POS CFSG.KD.G2Three.Sec1.Gen1.posK1
#kss_ntree CFSG.KD.G2Three.Sec1.R1K1SRT CFSG.KD.G2Three.Sec1.Gen1.srtK1
#kss_ntree CFSG.KD.G2Three.Sec1.R1K1SRI CFSG.KD.G2Three.Sec1.Gen1.sriK1
#kss_ntree CFSG.KD.G2Three.Sec1.R1K2G CFSG.KD.G2Three.Sec1.Gen1.gK2
#kss_ntree CFSG.KD.G2Three.Sec1.R1K2 CFSG.KD.G2Three.Sec1.Gen1.xK2L
#kss_ntree CFSG.KD.G2Three.Sec1.R1K2PA CFSG.KD.G2Three.Sec1.Gen1.paK2
#kss_ntree CFSG.KD.G2Three.Sec1.R1K2PB CFSG.KD.G2Three.Sec1.Gen1.pbK2
#kss_ntree CFSG.KD.G2Three.Sec1.R1K2POS CFSG.KD.G2Three.Sec1.Gen1.posK2
#kss_ntree CFSG.KD.G2Three.Sec1.R1K2SRT CFSG.KD.G2Three.Sec1.Gen1.srtK2
#kss_ntree CFSG.KD.G2Three.Sec1.R1K2SRI CFSG.KD.G2Three.Sec1.Gen1.sriK2
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q1G CFSG.KD.G2Three.Sec1.Gen1.gQ1
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q1 CFSG.KD.G2Three.Sec1.Gen1.xQ1L
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q1PA CFSG.KD.G2Three.Sec1.Gen1.paQ1
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q1PB CFSG.KD.G2Three.Sec1.Gen1.pbQ1
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q1POS CFSG.KD.G2Three.Sec1.Gen1.posQ1
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q1SRT CFSG.KD.G2Three.Sec1.Gen1.srtQ1
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q1SRI CFSG.KD.G2Three.Sec1.Gen1.sriQ1
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q2G CFSG.KD.G2Three.Sec1.Gen1.gQ2
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q2 CFSG.KD.G2Three.Sec1.Gen1.xQ2L
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q2PA CFSG.KD.G2Three.Sec1.Gen1.paQ2
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q2PB CFSG.KD.G2Three.Sec1.Gen1.pbQ2
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q2POS CFSG.KD.G2Three.Sec1.Gen1.posQ2
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q2SRT CFSG.KD.G2Three.Sec1.Gen1.srtQ2
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q2SRI CFSG.KD.G2Three.Sec1.Gen1.sriQ2
#kss_ntree CFSG.KD.G2Three.Sec1.R1SG CFSG.KD.G2Three.Sec1.Gen1.gS
#kss_ntree CFSG.KD.G2Three.Sec1.R1S CFSG.KD.G2Three.Sec1.Gen1.xSL
#kss_ntree CFSG.KD.G2Three.Sec1.R1SPA CFSG.KD.G2Three.Sec1.Gen1.paS
#kss_ntree CFSG.KD.G2Three.Sec1.R1SPB CFSG.KD.G2Three.Sec1.Gen1.pbS
#kss_ntree CFSG.KD.G2Three.Sec1.R1SPOS CFSG.KD.G2Three.Sec1.Gen1.posS
#kss_ntree CFSG.KD.G2Three.Sec1.R1SSRT CFSG.KD.G2Three.Sec1.Gen1.srtS
#kss_ntree CFSG.KD.G2Three.Sec1.R1SSRI CFSG.KD.G2Three.Sec1.Gen1.sriS
#kss_ntree CFSG.KD.G2Three.Sec1.R1AG CFSG.KD.G2Three.Sec1.Gen1.gA
#kss_ntree CFSG.KD.G2Three.Sec1.R1A CFSG.KD.G2Three.Sec1.Gen1.xAL
#kss_ntree CFSG.KD.G2Three.Sec1.R1APA CFSG.KD.G2Three.Sec1.Gen1.paA
#kss_ntree CFSG.KD.G2Three.Sec1.R1APB CFSG.KD.G2Three.Sec1.Gen1.pbA
#kss_ntree CFSG.KD.G2Three.Sec1.R1APOS CFSG.KD.G2Three.Sec1.Gen1.posA
#kss_ntree CFSG.KD.G2Three.Sec1.R1ASRT CFSG.KD.G2Three.Sec1.Gen1.srtA
#kss_ntree CFSG.KD.G2Three.Sec1.R1ASRI CFSG.KD.G2Three.Sec1.Gen1.sriA
#kss_ntree CFSG.KD.G2Three.Sec1.R1MG CFSG.KD.G2Three.Sec1.Gen1.gM
#kss_ntree CFSG.KD.G2Three.Sec1.R1M CFSG.KD.G2Three.Sec1.Gen1.xML
#kss_ntree CFSG.KD.G2Three.Sec1.R1MPA CFSG.KD.G2Three.Sec1.Gen1.paM
#kss_ntree CFSG.KD.G2Three.Sec1.R1MPB CFSG.KD.G2Three.Sec1.Gen1.pbM
#kss_ntree CFSG.KD.G2Three.Sec1.R1MPOS CFSG.KD.G2Three.Sec1.Gen1.posM
#kss_ntree CFSG.KD.G2Three.Sec1.R1MSRT CFSG.KD.G2Three.Sec1.Gen1.srtM
#kss_ntree CFSG.KD.G2Three.Sec1.R1MSRI CFSG.KD.G2Three.Sec1.Gen1.sriM
#kss_ntree CFSG.KD.G2Three.Sec1.R1IM CFSG.KD.G2Three.Sec1.Gen1.iM
#kss_ntree CFSG.KD.G2Three.Sec1.R1IMU CFSG.KD.G2Three.Sec1.Gen1.iMU
#kss_ntree CFSG.KD.G2Three.Sec1.R1EFG CFSG.KD.G2Three.Sec1.Gen1.gEF
#kss_ntree CFSG.KD.G2Three.Sec1.R1KG CFSG.KD.G2Three.Sec1.Gen1.kG

#kss_ntree CFSG.KD.G2Three.Sec1.R1EG CFSG.KD.G2Three.Sec1.Gen1.gE
#kss_ntree CFSG.KD.G2Three.Sec1.R1E CFSG.KD.G2Three.Sec1.Gen1.xEL
#kss_ntree CFSG.KD.G2Three.Sec1.R1ESRT CFSG.KD.G2Three.Sec1.Gen1.srtE
#kss_ntree CFSG.KD.G2Three.Sec1.R1ESRI CFSG.KD.G2Three.Sec1.Gen1.sriE
#kss_ntree CFSG.KD.G2Three.Sec1.R1FG CFSG.KD.G2Three.Sec1.Gen1.gF
#kss_ntree CFSG.KD.G2Three.Sec1.R1F CFSG.KD.G2Three.Sec1.Gen1.xFL
#kss_ntree CFSG.KD.G2Three.Sec1.R1FSRT CFSG.KD.G2Three.Sec1.Gen1.srtF
#kss_ntree CFSG.KD.G2Three.Sec1.R1FSRI CFSG.KD.G2Three.Sec1.Gen1.sriF
#kss_ntree CFSG.KD.G2Three.Sec1.R1Y2G CFSG.KD.G2Three.Sec1.Gen1.gY2
#kss_ntree CFSG.KD.G2Three.Sec1.R1Y2 CFSG.KD.G2Three.Sec1.Gen1.xY2L
#kss_ntree CFSG.KD.G2Three.Sec1.R1Y2SRT CFSG.KD.G2Three.Sec1.Gen1.srtY2
#kss_ntree CFSG.KD.G2Three.Sec1.R1Y2SRI CFSG.KD.G2Three.Sec1.Gen1.sriY2
#kss_ntree CFSG.KD.G2Three.Sec1.R1Y3G CFSG.KD.G2Three.Sec1.Gen1.gY3
#kss_ntree CFSG.KD.G2Three.Sec1.R1Y3 CFSG.KD.G2Three.Sec1.Gen1.xY3L
#kss_ntree CFSG.KD.G2Three.Sec1.R1Y3SRT CFSG.KD.G2Three.Sec1.Gen1.srtY3
#kss_ntree CFSG.KD.G2Three.Sec1.R1Y3SRI CFSG.KD.G2Three.Sec1.Gen1.sriY3
#kss_ntree CFSG.KD.G2Three.Sec1.R1Y2W CFSG.KD.G2Three.Sec1.Gen1.y2W
#kss_ntree CFSG.KD.G2Three.Sec1.R1Y3W CFSG.KD.G2Three.Sec1.Gen1.y3W

#kss_ntree CFSG.KD.G2Three.Sec1.R1KY CFSG.KD.G2Three.Sec1.Gen1.kYL
#kss_ntree CFSG.KD.G2Three.Sec1.R1KYSRT CFSG.KD.G2Three.Sec1.Gen1.srtKY
#kss_ntree CFSG.KD.G2Three.Sec1.R1KYSRI CFSG.KD.G2Three.Sec1.Gen1.sriKY
#kss_ntree CFSG.KD.G2Three.Sec1.R1PY CFSG.KD.G2Three.Sec1.Gen1.pYL
#kss_ntree CFSG.KD.G2Three.Sec1.R1PG CFSG.KD.G2Three.Sec1.Gen1.pGL
#kss_ntree CFSG.KD.G2Three.Sec1.R1PU CFSG.KD.G2Three.Sec1.Gen1.pUL
#kss_ntree CFSG.KD.G2Three.Sec1.R1PI CFSG.KD.G2Three.Sec1.Gen1.xPIL
#kss_ntree CFSG.KD.G2Three.Sec1.R1PIPA CFSG.KD.G2Three.Sec1.Gen1.paPI
#kss_ntree CFSG.KD.G2Three.Sec1.R1PIPB CFSG.KD.G2Three.Sec1.Gen1.pbPI
#kss_ntree CFSG.KD.G2Three.Sec1.R1PIPOS CFSG.KD.G2Three.Sec1.Gen1.posPI
#kss_ntree CFSG.KD.G2Three.Sec1.R1PISRT CFSG.KD.G2Three.Sec1.Gen1.srtPI
#kss_ntree CFSG.KD.G2Three.Sec1.R1PISRI CFSG.KD.G2Three.Sec1.Gen1.sriPI

#kss_ntree CFSG.KD.G2Three.Sec1.R1EMG CFSG.KD.G2Three.Sec1.Gen1.mG
#kss_ntree CFSG.KD.G2Three.Sec1.R1EM CFSG.KD.G2Three.Sec1.Gen1.mL

#kss_ntree CFSG.KD.G2Three.Sec1.R1NK1 CFSG.KD.G2Three.Sec1.Gen1.nK1
#kss_ntree CFSG.KD.G2Three.Sec1.R1NK2 CFSG.KD.G2Three.Sec1.Gen1.nK2
#kss_ntree CFSG.KD.G2Three.Sec1.R1NQ1 CFSG.KD.G2Three.Sec1.Gen1.nQ1
#kss_ntree CFSG.KD.G2Three.Sec1.R1NQ2 CFSG.KD.G2Three.Sec1.Gen1.nQ2
#kss_ntree CFSG.KD.G2Three.Sec1.R1NA5 CFSG.KD.G2Three.Sec1.Gen1.nA

#kss_ntree CFSG.KD.G2Three.Sec1.R1O1W CFSG.KD.G2Three.Sec1.Gen1.o1W
#kss_ntree CFSG.KD.G2Three.Sec1.R1O1K CFSG.KD.G2Three.Sec1.Gen1.o1K
#kss_ntree CFSG.KD.G2Three.Sec1.R1O1V CFSG.KD.G2Three.Sec1.Gen1.o1V
#kss_ntree CFSG.KD.G2Three.Sec1.R1O1E CFSG.KD.G2Three.Sec1.Gen1.o1E
#kss_ntree CFSG.KD.G2Three.Sec1.R1O2W CFSG.KD.G2Three.Sec1.Gen1.o2W
#kss_ntree CFSG.KD.G2Three.Sec1.R1O2K CFSG.KD.G2Three.Sec1.Gen1.o2K
#kss_ntree CFSG.KD.G2Three.Sec1.R1O2V CFSG.KD.G2Three.Sec1.Gen1.o2V
#kss_ntree CFSG.KD.G2Three.Sec1.R1O2E CFSG.KD.G2Three.Sec1.Gen1.o2E
#kss_ntree CFSG.KD.G2Three.Sec1.R1O3W CFSG.KD.G2Three.Sec1.Gen1.o3W
#kss_ntree CFSG.KD.G2Three.Sec1.R1O3K CFSG.KD.G2Three.Sec1.Gen1.o3K
#kss_ntree CFSG.KD.G2Three.Sec1.R1O3V CFSG.KD.G2Three.Sec1.Gen1.o3V
#kss_ntree CFSG.KD.G2Three.Sec1.R1O3E CFSG.KD.G2Three.Sec1.Gen1.o3E

#kss_ntree CFSG.KD.G2Three.Sec1.R1RAR CFSG.KD.G2Three.Sec1.Gen1.raL
#kss_ntree CFSG.KD.G2Three.Sec1.R1RAW CFSG.KD.G2Three.Sec1.Gen1.raW
#kss_ntree CFSG.KD.G2Three.Sec1.R1RAT CFSG.KD.G2Three.Sec1.Gen1.raT
#kss_ntree CFSG.KD.G2Three.Sec1.R1RAE CFSG.KD.G2Three.Sec1.Gen1.raE
#kss_ntree CFSG.KD.G2Three.Sec1.R1P4I CFSG.KD.G2Three.Sec1.Gen1.p4I
#kss_ntree CFSG.KD.G2Three.Sec1.R1P4J CFSG.KD.G2Three.Sec1.Gen1.p4J
#kss_ntree CFSG.KD.G2Three.Sec1.R1EO CFSG.KD.G2Three.Sec1.Gen1.eo
#kss_ntree CFSG.KD.G2Three.Sec1.R1ETU CFSG.KD.G2Three.Sec1.Gen1.etU
#kss_ntree CFSG.KD.G2Three.Sec1.R1ETV CFSG.KD.G2Three.Sec1.Gen1.etV
#kss_ntree CFSG.KD.G2Three.Sec1.R1ETK CFSG.KD.G2Three.Sec1.Gen1.etK
#kss_ntree CFSG.KD.G2Three.Sec1.R1FXK CFSG.KD.G2Three.Sec1.Gen1.fxK
#kss_ntree CFSG.KD.G2Three.Sec1.R1CE CFSG.KD.G2Three.Sec1.Gen1.ceL
#kss_ntree CFSG.KD.G2Three.Sec1.R1EDI CFSG.KD.G2Three.Sec1.Gen1.edI
#kss_ntree CFSG.KD.G2Three.Sec1.R1EDJ CFSG.KD.G2Three.Sec1.Gen1.edJ
#kss_ntree CFSG.KD.G2Three.Sec1.R1EDD CFSG.KD.G2Three.Sec1.Gen1.edD
#kss_ntree CFSG.KD.G2Three.Sec1.R1EDW CFSG.KD.G2Three.Sec1.Gen1.edW
