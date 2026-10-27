module

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

namespace CertificateChecks.KernelFi24F3d

abbrev KP (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

@[expose] def KP.Disj {n : ℕ} (p q : KP n) : Prop :=
  p.1.1 ≠ q.1.1 ∧ p.1.1 ≠ q.1.2 ∧ p.1.2 ≠ q.1.1 ∧ p.1.2 ≠ q.1.2

instance KP.decDisj {n : ℕ} : DecidableRel (@KP.Disj n) := fun p q => by
  unfold KP.Disj
  infer_instance

theorem card_KP9 : Fintype.card (KP 9) = 36 := by decide

theorem card_KP7 : Fintype.card (KP 7) = 21 := by decide

theorem KP.disj_irrefl {n : ℕ} (p : KP n) : ¬ KP.Disj p p := fun h => h.1 rfl

theorem KP9_nbr : ∀ p : KP 9, ∃ q, KP.Disj p q := by decide

theorem KP9_common : ∀ p q : KP 9, p ≠ q → ¬ KP.Disj p q → ∃ r, KP.Disj r p ∧ KP.Disj r q := by
  decide

@[expose] def KP.chain {n : ℕ} (i : ℕ) (h : i + 1 < n) : KP n :=
  ⟨(⟨i, by omega⟩, ⟨i + 1, h⟩), by simp [Fin.lt_def]⟩

theorem chain_succ {n i j : ℕ} (hi : i + 1 < n) (hj : j + 1 < n) (hij : i + 1 = j) :
    KP.chain i hi ≠ KP.chain j hj ∧ ¬ KP.Disj (KP.chain i hi) (KP.chain j hj) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := congrArg (fun p : KP n => p.1.1.val) h
    simp [KP.chain] at this
    omega
  · apply h.2.2.1
    apply Fin.ext
    simp [KP.chain]
    omega

theorem chain_far {n i j : ℕ} (hi : i + 1 < n) (hj : j + 1 < n) (hij : i + 2 ≤ j) :
    KP.Disj (KP.chain i hi) (KP.chain j hj) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> have := congrArg Fin.val h <;> simp [KP.chain] at this <;>
    omega

end CertificateChecks.KernelFi24F3d

end
