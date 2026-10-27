module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion

public section

namespace CertificateChecks.KernelU43CentPlus

open Subgroup

theorem q8_central : ∀ x y : QuaternionGroup 2, (∀ u : QuaternionGroup 2, x * u = u * x) →
    x ≠ 1 → y * y ≠ 1 → x = y * y := by
  decide

theorem q8_fourth : ∀ x : QuaternionGroup 2, x * x * (x * x) = 1 := by decide

theorem q8_card_roots : (Finset.univ.filter fun x : QuaternionGroup 2 => x * x ≠ 1).card = 6 := by
  decide

variable {G : Type*} [Group G] {K : Subgroup G}

theorem sq_ne_one_of_equiv (e : K ≃* QuaternionGroup 2) {a : K} (ha : (a : G) * a ≠ 1) :
    e a * e a ≠ 1 := fun h => ha (by
  have h' : a * a = 1 := e.injective (by rw [map_mul, h, map_one])
  simpa using congrArg Subtype.val h')

theorem sq_ne_one_of_equiv_symm (e : K ≃* QuaternionGroup 2) {q : QuaternionGroup 2}
    (hq : q * q ≠ 1) : ((e.symm q : K) : G) * (e.symm q : K) ≠ 1 := fun h => hq (by
  have h' : e.symm q * e.symm q = 1 := Subtype.ext (by simpa using h)
  rw [← e.apply_symm_apply q, ← map_mul, h', map_one])

theorem central_eq_sq (e : K ≃* QuaternionGroup 2) {z y : G} (hz : z ∈ K)
    (hc : ∀ u ∈ K, z * u = u * z) (hz1 : z ≠ 1) (hy : y ∈ K) (hy1 : y * y ≠ 1) : z = y * y := by
  have hc' : ∀ u : QuaternionGroup 2, e ⟨z, hz⟩ * u = u * e ⟨z, hz⟩ := fun u => by
    rw [← e.apply_symm_apply u, ← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hc _ (e.symm u).2))
  have hz1' : e ⟨z, hz⟩ ≠ 1 := fun h => hz1 (by
    simpa using congrArg Subtype.val ((MulEquiv.map_eq_one_iff e).1 h))
  have h := q8_central _ _ hc' hz1' (sq_ne_one_of_equiv e (a := ⟨y, hy⟩) hy1)
  rw [← map_mul] at h
  simpa using congrArg Subtype.val (e.injective h)

theorem fourth_eq_one (e : K ≃* QuaternionGroup 2) {x : G} (hx : x ∈ K) : x * x * (x * x) = 1 := by
  have h := q8_fourth (e ⟨x, hx⟩)
  rw [← map_mul, ← map_mul, MulEquiv.map_eq_one_iff] at h
  simpa using congrArg Subtype.val h

theorem ncard_roots (e : K ≃* QuaternionGroup 2) : {y | y ∈ K ∧ y * y ≠ 1}.ncard = 6 := by
  have h : {y | y ∈ K ∧ y * y ≠ 1} =
      (fun q => ((e.symm q : K) : G)) '' {q : QuaternionGroup 2 | q * q ≠ 1} := by
    ext y
    constructor
    · rintro ⟨hy, hy1⟩
      exact ⟨e ⟨y, hy⟩, sq_ne_one_of_equiv e (a := ⟨y, hy⟩) hy1, by simp⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨(e.symm q).2, sq_ne_one_of_equiv_symm e hq⟩
  have hinj : Function.Injective fun q : QuaternionGroup 2 => ((e.symm q : K) : G) :=
    Subtype.val_injective.comp e.symm.injective
  rw [h, Set.ncard_image_of_injective _ hinj,
    Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
  exact q8_card_roots

theorem card_of_equiv (e : K ≃* QuaternionGroup 2) : Nat.card K = 8 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem eight_roots {Q₁ Q₂ : Subgroup G} (e₁ : Q₁ ≃* QuaternionGroup 2)
    (e₂ : Q₂ ≃* QuaternionGroup 2) (hc : ⁅Q₁, Q₂⁆ = ⊥) (hcard : Nat.card ↥(Q₁ ⊔ Q₂) = 32)
    {g : G} (hg : g ∈ Q₁) (hg1 : g * g ≠ 1) :
    8 ≤ {h | h ∈ Q₁ ⊔ Q₂ ∧ h * g = g * h ∧ h * h = g * g}.ncard := by
  have hcomm : ∀ x ∈ Q₁, ∀ y ∈ Q₂, y * x = x * y := fun x hx y hy =>
    mem_centralizer_iff.1 ((commutator_eq_bot_iff_le_centralizer.1 hc) hx) y hy
  have hfin : Finite ↥(Q₁ ⊔ Q₂) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨w, hw1, hw2, hw⟩ : ∃ w, w ∈ Q₁ ∧ w ∈ Q₂ ∧ w ≠ 1 := by
    by_contra! hne
    let f : Q₁ × Q₂ → ↥(Q₁ ⊔ Q₂) := fun p =>
      ⟨p.1 * p.2, mul_mem_sup p.1.2 p.2.2⟩
    have hf : Function.Injective f := by
      rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ e
      have e' : x * y = x' * y' := congrArg Subtype.val e
      have h1 : x'⁻¹ * x = y' * y⁻¹ := by
        calc x'⁻¹ * x = x'⁻¹ * (x * y) * y⁻¹ := by group
          _ = x'⁻¹ * (x' * y') * y⁻¹ := by rw [e']
          _ = y' * y⁻¹ := by group
      have h2 : x'⁻¹ * x = 1 :=
        hne _ (Q₁.mul_mem (Q₁.inv_mem hx') hx) (h1 ▸ Q₂.mul_mem hy' (Q₂.inv_mem hy))
      have hxx : x' = x := inv_mul_eq_one.1 h2
      subst hxx
      have hyy : y = y' := mul_left_cancel e'
      subst hyy
      rfl
    have h := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod, card_of_equiv e₁, card_of_equiv e₂, hcard] at h
    norm_num at h
  have hw_1 : w = g * g := central_eq_sq e₁ hw1 (fun u hu => (hcomm u hu w hw2)) hw hg hg1
  have hw_2 : ∀ y ∈ Q₂, y * y ≠ 1 → y * y = g * g := fun y hy hy1 =>
    hw_1 ▸ (central_eq_sq e₂ hw2 (fun u hu => (hcomm w hw1 u hu).symm) hw hy hy1).symm
  have hgQ2 : g ∉ Q₂ := fun h => by
    have := central_eq_sq e₁ hg (fun u hu => hcomm u hu g h)
      (fun h1 => hg1 (by rw [h1, mul_one])) hg hg1
    exact hg1 (by
      have h1 : g = 1 := by
        have : g * 1 = g * g := by rw [mul_one]; exact this
        exact (mul_left_cancel this).symm
      rw [h1, mul_one])
  have hgi : g⁻¹ ≠ g := fun h => hg1 (by
    calc g * g = g * g⁻¹ := by rw [h]
      _ = 1 := mul_inv_cancel g)
  have hgi2 : g⁻¹ * g⁻¹ = g * g := by
    rw [← mul_inv_rev]
    exact inv_eq_of_mul_eq_one_right (fourth_eq_one e₁ hg)
  set R := {y | y ∈ Q₂ ∧ y * y ≠ 1}
  have hfin2 : Finite Q₂ := Nat.finite_of_card_ne_zero (by rw [card_of_equiv e₂]; norm_num)
  have hRfin : R.Finite := (Set.toFinite (Q₂ : Set G)).subset fun y hy => hy.1
  have hS : insert g (insert g⁻¹ R) ⊆ {h | h ∈ Q₁ ⊔ Q₂ ∧ h * g = g * h ∧ h * h = g * g} := by
    rintro h (rfl | rfl | ⟨hy, hy1⟩)
    · exact ⟨mem_sup_left hg, rfl, rfl⟩
    · exact ⟨mem_sup_left (Q₁.inv_mem hg), by group, hgi2⟩
    · exact ⟨mem_sup_right hy, hcomm g hg h hy, hw_2 h hy hy1⟩
  have hT : {h | h ∈ Q₁ ⊔ Q₂ ∧ h * g = g * h ∧ h * h = g * g}.Finite :=
    (Set.toFinite ((Q₁ ⊔ Q₂ : Subgroup G) : Set G)).subset fun h hh => hh.1
  have hcardS : (insert g (insert g⁻¹ R)).ncard = 8 := by
    rw [Set.ncard_insert_of_notMem _ (hRfin.insert _), Set.ncard_insert_of_notMem _ hRfin,
      ncard_roots e₂]
    · exact fun h => hgQ2 (by simpa using Q₂.inv_mem h.1)
    · rintro (h | h)
      · exact hgi h.symm
      · exact hgQ2 h.1
  rw [← hcardS]
  exact Set.ncard_le_ncard hS hT

end CertificateChecks.KernelU43CentPlus

end
