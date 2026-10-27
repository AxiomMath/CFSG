module

public import Certificates.Kernel.LocalQT.PEnumD
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Sporadic.SmallOddCore.HSCosetInputs
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HSL

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore

meta def idM : Array Nat := idTab 3850
meta def qgM : Array (Array Nat) := hsQGens
meta def dgM : Array (Array Nat) := hsDGens
meta def diM : Array (Array Nat) := hsDInvs

meta def rM (l : Nat) : Array Nat := wordTabS 3850 hsDGens (hsDClassWords.getD l [])

meta def r0M : Array Nat := rM 0
meta def r1M : Array Nat := rM 1
meta def r2M : Array Nat := rM 2
meta def r3M : Array Nat := rM 3
meta def r4M : Array Nat := rM 4
meta def r5M : Array Nat := rM 5
meta def r6M : Array Nat := rM 6
meta def cosM : Array (Array Nat) := hsCosTabs
meta def cosIM : Array (Array Nat) := hsCosInvs

meta def normM (E : Enum) (gens ginv gs : Array (Array Nat)) (first : Bool) :
    Array (Array Nat) :=
  let idx := indexOf E.tabs
  ((List.range gens.size).toArray.map fun j => (List.range gs.size).toArray.map fun i =>
    let x := if first then conjTab 3850 gens[j]! ginv[j]! gs[i]!
      else conjTab 3850 ginv[j]! gens[j]! gs[i]!
    #[idx.getD x 0]).flatten

meta def nq1M : Array (Array Nat) := normM hsQEnum hsC1Tabs hsC1Invs hsQGens true
meta def nq2M : Array (Array Nat) := normM hsQEnum hsC1Tabs hsC1Invs hsQGens false
meta def nd1M : Array (Array Nat) := normM hsDEnum hsC2Tabs hsC2Invs hsDGens true
meta def nd2M : Array (Array Nat) := normM hsDEnum hsC2Tabs hsC2Invs hsDGens false

meta def coverM : Array (Array Nat) :=
  let idxs := hsDOrbits.map fun e => indexOf e.tabs
  hsDEnum.tabs.map fun t =>
    let l := ((List.range 7).find? fun l => (idxs[l]!).contains t).getD 0
    #[65536 * l + (idxs[l]!).getD t 0]

end CFSG.KD.HSL

#kpenum_d CFSG.KD.HSL.Q 3850 12 false CFSG.KD.HSL.qgM CFSG.KD.HSL.qgM CFSG.KD.HSL.idM 64
#kpenum_d CFSG.KD.HSL.D 3850 12 false CFSG.KD.HSL.dgM CFSG.KD.HSL.dgM CFSG.KD.HSL.idM 360
#kpenum_d CFSG.KD.HSL.O0 3850 12 true CFSG.KD.HSL.dgM CFSG.KD.HSL.diM CFSG.KD.HSL.r0M 1000
#kpenum_d CFSG.KD.HSL.O1 3850 12 true CFSG.KD.HSL.dgM CFSG.KD.HSL.diM CFSG.KD.HSL.r1M 1000
#kpenum_d CFSG.KD.HSL.O2 3850 12 true CFSG.KD.HSL.dgM CFSG.KD.HSL.diM CFSG.KD.HSL.r2M 1000
#kpenum_d CFSG.KD.HSL.O3 3850 12 true CFSG.KD.HSL.dgM CFSG.KD.HSL.diM CFSG.KD.HSL.r3M 1000
#kpenum_d CFSG.KD.HSL.O4 3850 12 true CFSG.KD.HSL.dgM CFSG.KD.HSL.diM CFSG.KD.HSL.r4M 1000
#kpenum_d CFSG.KD.HSL.O5 3850 12 true CFSG.KD.HSL.dgM CFSG.KD.HSL.diM CFSG.KD.HSL.r5M 1000
#kpenum_d CFSG.KD.HSL.O6 3850 12 true CFSG.KD.HSL.dgM CFSG.KD.HSL.diM CFSG.KD.HSL.r6M 1000
#kmisc_packarrs CFSG.KD.HSL.CS CFSG.KD.HSL.cosM 12
#kmisc_packarrs CFSG.KD.HSL.CSI CFSG.KD.HSL.cosIM 12
#kmisc_packarrs CFSG.KD.HSL.NQ1 CFSG.KD.HSL.nq1M 32
#kmisc_packarrs CFSG.KD.HSL.NQ2 CFSG.KD.HSL.nq2M 32
#kmisc_packarrs CFSG.KD.HSL.ND1 CFSG.KD.HSL.nd1M 32
#kmisc_packarrs CFSG.KD.HSL.ND2 CFSG.KD.HSL.nd2M 32
#kmisc_packarrs CFSG.KD.HSL.COV CFSG.KD.HSL.coverM 32

end
