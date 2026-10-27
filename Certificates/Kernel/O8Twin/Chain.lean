module

public import CFSG.Certificates.Kernel.Spor.RawSound
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.SporSch.Mathieu.Gen
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Mathieu.Gen
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

namespace CertificateChecks.KernelO8Twin

open CFSG.KS.SporSch.MOCG

meta def gensT : Array (Array Nat) :=
  #[0, 2, 4, 6].map fun i => (CFSG.EvenSmallLie.OmegaEight.genArrs[i]!).extract 0 120

@[expose] def sDeriveT : List (List Int) := [[-2, 3, 2], [-5, 4, 5], [-4, -2, 4, 2]]

meta def sDeriveM : List (List Int) := [[-2, 3, 2], [-5, 4, 5], [-4, -2, 4, 2]]

meta def strongT : Array (Array Nat) := strongOf 120 gensT sDeriveM

meta def baseT : Array Nat := #[0, 2, 4, 24, 8]

end CertificateChecks.KernelO8Twin

#ks_rawchain CertificateChecks.KernelO8Twin.ST 120 7 24 CertificateChecks.KernelO8Twin.strongT
  CertificateChecks.KernelO8Twin.baseT 4 CertificateChecks.KernelO8Twin.sDeriveT

end
