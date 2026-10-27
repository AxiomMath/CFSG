module

public import Certificates.Data.CFSGNative.Co3Schreier.Basic
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi22Data
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

namespace CertificateChecks.KernelSpor.Fo22W

open CFSG.Sporadic.FischerOddCore CFSG.Sporadic.Schreier.Co3.Native

@[expose] def n3D : List (List Int) := fo22N3Words.toList.drop 2
@[expose] def p3D : List (List Int) := fo22P3Words.toList.drop 2
@[expose] def n4D : List (List Int) := fo22N4Words.toList.drop 2
@[expose] def p4D : List (List Int) := fo22P4Words.toList.drop 2
@[expose] def p2D : List (List Int) := fo22P2Words.toList.drop 3

theorem n3W : fo22N3Words = wordsArr 2 7 n3D := by decide +kernel
theorem p3W : fo22P3Words = wordsArr 2 11 p3D := by decide +kernel
theorem n4W : fo22N4Words = wordsArr 2 7 n4D := by decide +kernel
theorem p4W : fo22P4Words = wordsArr 2 11 p4D := by decide +kernel
theorem p2W : fo22P2Words = wordsArr 3 11 p2D := by decide +kernel

end CertificateChecks.KernelSpor.Fo22W

end
