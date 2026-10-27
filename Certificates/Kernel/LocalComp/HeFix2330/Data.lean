module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixTwoBCheckInputs
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

namespace CertificateChecks.KernelLC.HeFix2330

open CFSG.ComponentClassification.GrSLit.HeldFix

meta def commM : Array (Array Nat) := hfCommTabs42

meta def ord7M : Array (Array Nat) := hfOrd7Tabs42

meta def ord3M : Array (Array Nat) := hfOrd3Tabs42

meta def id42 : Array Nat := CFSG.PSL3Four.Native.idTab 42

end CertificateChecks.KernelLC.HeFix2330

public section

set_option maxRecDepth 400000

#kpenum CertificateChecks.KernelLC.HCE 42 6 false CertificateChecks.KernelLC.HeFix2330.commM
  CertificateChecks.KernelLC.HeFix2330.commM CertificateChecks.KernelLC.HeFix2330.id42 10752

#kpenum CertificateChecks.KernelLC.HSE 42 6 false CertificateChecks.KernelLC.HeFix2330.ord7M
  CertificateChecks.KernelLC.HeFix2330.ord7M CertificateChecks.KernelLC.HeFix2330.id42 10752

#kpenum CertificateChecks.KernelLC.HTE 42 6 false CertificateChecks.KernelLC.HeFix2330.ord3M
  CertificateChecks.KernelLC.HeFix2330.ord3M CertificateChecks.KernelLC.HeFix2330.id42 10752

end
