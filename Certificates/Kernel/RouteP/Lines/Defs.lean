module

public import Certificates.Kernel.RouteP.Data.Pres
public import Certificates.Kernel.RouteP.Data.Y332
public import Certificates.Data.Kernel.RouteP.Lines
public import Certificates.Kernel.RouteP.Text.Texts
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

namespace CFSG.KD.RouteP

open CFSG.KC CFSG.KC.RouteP

@[expose] noncomputable def olck (g : Nat) : Bool :=
  lineOK NWO KAO KBO CertificateChecks.KernelRouteP.objLinesK.toArray 0 (fun ℓ => 2 + ℓ) g

@[expose] noncomputable def plck (g : Nat) : Bool :=
  lineOK NWP KAP KBP CertificateChecks.KernelRouteP.presLinesK.toArray 0 (fun ℓ => 2 + ℓ) g

@[expose] def bgT (ℓ : Nat) : Nat := [39, 40, 0, 1].getD ℓ 0

@[expose] noncomputable def bgck (g : Nat) : Bool :=
  lineOK NWP KAP KBP CertificateChecks.KernelRouteP.bridgeGensLinesK.toArray 28 bgT g

@[expose] noncomputable def ylck (g : Nat) : Bool :=
  lineOK NWY KAY KBY CertificateChecks.KernelRouteP.y332LinesK.toArray 0 (fun ℓ => 2 + ℓ) g

end CFSG.KD.RouteP

end
