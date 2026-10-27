module

public meta import CFSG.Sporadic.ONOddCore.QuotOuterCheckInputs
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

namespace CertificateChecks.KernelSpor.ON2127

open CFSG.Sporadic.ONOddCore

meta def pairG (k : Nat) : Array (Array Nat) := pairGens (localCert.records.getD k default)

meta def g0 : Array (Array Nat) := pairG 0
meta def g1 : Array (Array Nat) := pairG 1
meta def g2 : Array (Array Nat) := pairG 2
meta def g3 : Array (Array Nat) := pairG 3
meta def g4 : Array (Array Nat) := pairG 4
meta def g5 : Array (Array Nat) := pairG 5
meta def g6 : Array (Array Nat) := pairG 6
meta def g7 : Array (Array Nat) := pairG 7
meta def g8 : Array (Array Nat) := pairG 8
meta def g9 : Array (Array Nat) := pairG 9
meta def g10 : Array (Array Nat) := pairG 10
meta def g11 : Array (Array Nat) := pairG 11

meta def id240 : Array Nat := CFSG.PSL3Four.Native.idTab 240

end CertificateChecks.KernelSpor.ON2127

end
