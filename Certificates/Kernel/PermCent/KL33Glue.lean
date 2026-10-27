module

public import Certificates.Kernel.PermCent.KL33Rep
public import Certificates.Kernel.PermCent.KL33Syl
public import CFSG.Certificates.Kernel.PermCent.SylowListSound
public import CFSG.Certificates.Kernel.PermCent.L33RepPred
public import CFSG.GH74.KGroups.L33

public section

namespace CFSG.Certificates.Kernel.PkCV.L33R.Glue

open Subgroup CFSG.GH74.KGroups CFSG.GH74.KGroups.L33 CFSG.Sporadic.Schreier
  CFSG.ClassicalInvolution.Q3.TA3 CFSG.Certificates.Kernel.PkCV.SylL
  CFSG.Certificates.Kernel.PkCV.L33R.KSyl CFSG.Certificates.Kernel.PkCV.L33R.KRep

theorem QA_closure : QA.originalSubgroup = closure {σ | σ ∈ gA.map ev} := by
  rw [QA, certificate_originalSubgroup]
  simp only [gA, List.map_cons, List.map_nil, ev_cOf]

theorem QP_le_QA : QP.originalSubgroup ≤ QA.originalSubgroup := by
  rw [QP_closure, closure_le, QA_closure]
  intro g hg
  apply Subgroup.subset_closure
  rcases hg with rfl | hg
  · simp [gA, ev_cOf]
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    simp [gA, ev_cOf]

theorem card_QA : Nat.card QA.originalSubgroup = 2 ^ 5 * 351 := by
  rw [card_group QA QA_ok, QA_valid.2]
  norm_num

theorem l33_normal :
    (QP.originalSubgroup.subgroupOf QA.originalSubgroup).Normal := by
  have hNcard : Nat.card (QP.originalSubgroup.subgroupOf QA.originalSubgroup) = 5616 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe QP_le_QA).toEquiv, card_group QP QP_ok, QP_valid.2]
  have h := card_mul_index (QP.originalSubgroup.subgroupOf QA.originalSubgroup)
  rw [hNcard, card_QA] at h
  exact normal_of_index_eq_two (by omega)

theorem l33_conj_mem :
    ∀ g ∈ QA.originalSubgroup, ∀ y ∈ QP.originalSubgroup, g * y * g⁻¹ ∈ QP.originalSubgroup := by
  intro g hg y hy
  have h := l33_normal.conj_mem ⟨y, QP_le_QA hy⟩ (mem_subgroupOf.2 hy) ⟨g, hg⟩
  rwa [mem_subgroupOf] at h

theorem l33_invol (Φ : Equiv.Perm (Fin 26) → Prop)
    (hΦ : ∀ g ∈ QA.originalSubgroup, ∀ x ∈ QA.originalSubgroup, Φ (g * x * g⁻¹) → Φ x)
    (hR : ∀ ρ ∈ reps, Φ (ev ρ)) :
    ∀ x ∈ QA.originalSubgroup, x ^ 2 = 1 → x ≠ 1 → Φ x :=
  forall_invol_of_checks QA.originalSubgroup gA tGens reps tElts covW QA_closure.ge
    ((closure_words_le gA tGenW).trans QA_closure.ge) (mem_of_words tGens tEltW) kClosed kCover
    (k := 5) (m := 351) (by norm_num) kLen card_QA (by decide) Φ hΦ hR

theorem l33_oddCore :
    ∀ τ ∈ QA.originalSubgroup, τ ^ 2 = 1 → τ ≠ 1 → ∀ x ∈ QA.originalSubgroup,
      x * τ = τ * x → x ≠ 1 → Odd (orderOf x) →
      ∃ c ∈ QP.originalSubgroup, c * τ = τ * c ∧ Even (orderOf (x * c * x⁻¹ * c⁻¹)) := by
  have hrep : ∀ {τ : CV 26}, oddCoreRepC 351 (elemsC QA) (elemsC QP) τ = true →
      OddCoreAtP QP.originalSubgroup QA.originalSubgroup (ev τ) := fun h =>
    oddCoreRep_sound QA QP QA_ok QP_ok QP_le_QA (by decide) card_QA h
  refine l33_invol (OddCoreAtP QP.originalSubgroup QA.originalSubgroup)
    (fun g hg _ _ h => oddCoreAtP_of_conj l33_conj_mem hg h) fun ρ hρ => ?_
  simp only [reps, List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl
  · exact hrep kOddInner
  · exact hrep kOddOuter

theorem l33_goodOrInner :
    ∀ t : QA.originalSubgroup, orderOf t = 2 →
      GoodOrInnerPred (QP.originalSubgroup.subgroupOf QA.originalSubgroup) t := by
  have hrep : ∀ {τ : CV 26}, goodAtC 100 (elemsC QP) (elemsC QA) τ = true →
      ∀ hτ : ev τ ∈ QA.originalSubgroup,
        GoodOrInnerPred (QP.originalSubgroup.subgroupOf QA.originalSubgroup) ⟨ev τ, hτ⟩ :=
    fun h hτ => goodAt_sound QA QP QA_ok QP_ok hτ h
  have key := l33_invol
    (fun x => ∀ hx : x ∈ QA.originalSubgroup,
      GoodOrInnerPred (QP.originalSubgroup.subgroupOf QA.originalSubgroup) ⟨x, hx⟩)
    (fun g hg _ _ h => goodOrInnerPred_of_conj l33_conj_mem hg h) fun ρ hρ => by
      simp only [reps, List.mem_cons, List.not_mem_nil, or_false] at hρ
      rcases hρ with rfl | rfl
      · exact hrep kGoodInner
      · exact hrep kGoodOuter
  intro t ht
  have h2 : (t : Equiv.Perm (Fin 26)) ^ 2 = 1 := by
    rw [← coe_pow, ← ht, pow_orderOf_eq_one, coe_one]
  have h1 : (t : Equiv.Perm (Fin 26)) ≠ 1 := fun e => by
    have : t = 1 := Subtype.ext e
    rw [this, orderOf_one] at ht
    omega
  exact key t t.2 h2 h1 t.2

end CFSG.Certificates.Kernel.PkCV.L33R.Glue

end
