module

public import Mathlib.GroupTheory.Sylow
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

public section

namespace CertificateChecks.KernelSporSch.PJ3Group

open scoped Pointwise

variable {K : Type*} [Group K] [Finite K]

omit [Finite K] in
theorem card_class_mul (x : K) :
    Nat.card {y : K // IsConj x y} * Nat.card {g : K // g * x = x * g} = Nat.card K := by
  have e1 : {y : K // IsConj x y} ≃ MulAction.orbit (ConjAct K) x :=
    Equiv.subtypeEquivRight fun y => by rw [ConjAct.mem_orbit_conjAct, isConj_comm]
  have e2 : {g : K // g * x = x * g} ≃ MulAction.stabilizer (ConjAct K) x :=
    { toFun := fun g => ⟨ConjAct.toConjAct g.1, by
        rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, g.2,
          mul_inv_cancel_right]⟩
      invFun := fun c => ⟨ConjAct.ofConjAct c.1, by
        have h := c.2
        rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def] at h
        calc ConjAct.ofConjAct c.1 * x
            = ConjAct.ofConjAct c.1 * x * (ConjAct.ofConjAct c.1)⁻¹ * ConjAct.ofConjAct c.1 := by
              group
          _ = x * ConjAct.ofConjAct c.1 := by rw [h]⟩
      left_inv := fun g => rfl
      right_inv := fun c => rfl }
  rw [Nat.card_congr e1, Nat.card_congr e2, ← Nat.card_prod,
    Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct K) x)]
  rfl

theorem exists_conj_mem {p : ℕ} [Fact p.Prime] (P : Subgroup K)
    (hP : Nat.card P = p ^ (Nat.card K).factorization p) {x : K} {k : ℕ} (hx : orderOf x = p ^ k) :
    ∃ g : K, g * x * g⁻¹ ∈ P := by
  have hX : IsPGroup p (Subgroup.zpowers x) := IsPGroup.of_card (by rw [Nat.card_zpowers, hx])
  obtain ⟨Q, hQ⟩ := hX.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q (Sylow.ofCard P hP)
  refine ⟨g, ?_⟩
  have hxQ : x ∈ (Q : Subgroup K) := hQ (Subgroup.mem_zpowers x)
  have h1 : MulAut.conj g • x ∈ MulAut.conj g • (Q : Subgroup K) :=
    Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) _ hxQ
  rw [← Sylow.coe_subgroup_smul, hg, Sylow.coe_ofCard] at h1
  exact h1

theorem factorization_eq {p a m k : ℕ} (hp : p.Prime) (hm : ¬p ∣ m) (h : a = p ^ k * m) :
    a.factorization p = k := by
  subst h
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0, Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, hp.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd hm]
  simp

omit [Finite K] in
theorem pow_mem_of_closed {s : Set K} (hmul : ∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) {g : K} (hg : g ∈ s) :
    ∀ k, g ^ (k + 1) ∈ s
  | 0 => by simpa using hg
  | k + 1 => by
    rw [pow_succ]
    exact hmul _ (pow_mem_of_closed hmul hg k) _ hg

def mulClosed (s : Set K) (hmul : ∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) (g₀ : K) (h₀ : g₀ ∈ s) :
    Subgroup K where
  carrier := s
  mul_mem' := fun ha hb => hmul _ ha _ hb
  one_mem' := by
    have h := pow_mem_of_closed hmul h₀ (orderOf g₀ - 1)
    rwa [Nat.sub_add_cancel (orderOf_pos g₀), pow_orderOf_eq_one] at h
  inv_mem' := fun {g} hg => by
    rcases Nat.lt_or_ge 1 (orderOf g) with h | h
    · have h1 := pow_mem_of_closed hmul hg (orderOf g - 2)
      have e : orderOf g - 2 + 1 = orderOf g - 1 := by omega
      rw [e] at h1
      have e2 : g ^ (orderOf g - 1) = g⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel (orderOf_pos g),
          pow_orderOf_eq_one]
      rwa [e2] at h1
    · have h1 : orderOf g = 1 := le_antisymm h (orderOf_pos g)
      rw [orderOf_eq_one_iff] at h1
      subst h1
      rw [inv_one]
      have h := pow_mem_of_closed hmul h₀ (orderOf g₀ - 1)
      rwa [Nat.sub_add_cancel (orderOf_pos g₀), pow_orderOf_eq_one] at h

theorem mem_mulClosed {s : Set K} {hmul : ∀ a ∈ s, ∀ b ∈ s, a * b ∈ s} {g₀ : K} {h₀ : g₀ ∈ s}
    {g : K} : g ∈ mulClosed s hmul g₀ h₀ ↔ g ∈ s :=
  Iff.rfl

end CertificateChecks.KernelSporSch.PJ3Group

end
