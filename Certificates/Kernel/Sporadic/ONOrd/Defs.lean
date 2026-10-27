module

public import Certificates.Kernel.Sporadic.ON.Data
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

namespace CertificateChecks.KernelSpor.ONOrd

open CFSG.KC.Enum CertificateChecks.KernelSpor.ON

@[expose] noncomputable def fA (x : Nat) : Nat := strictN x (TT 0)

@[expose] noncomputable def fB (x : Nat) : Nat := strictN x (TT 1)

@[expose] noncomputable def fAI (x : Nat) : Nat := strictN x (UU 0)

@[expose] noncomputable def fBI (x : Nat) : Nat := strictN x (UU 1)

@[expose] noncomputable def powK (F : Nat → Nat) (k x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ acc => F acc) k

@[expose] noncomputable def codeK (c x : Nat) : Nat :=
  nIf(Nat.beq c 0, fA x, nIf(Nat.beq c 1, fAI x, nIf(Nat.beq c 2, fB x, fBI x)))

@[expose] def o8W : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 2, 2, 0, 3, 1, 3, 3, 1, 2]

@[expose] noncomputable def o8K (x : Nat) : Nat := o8W.foldr codeK x

end CertificateChecks.KernelSpor.ONOrd

end
