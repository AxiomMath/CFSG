module

public import Certificates.Kernel.U43CentPlus.Plus
public import CFSG.LieType.Multipliers.U43Action
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.Commutator.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43CentPlus

open CFSG.KC.Enum CFSG.KC.U43Mod CFSG.KC.U43CentPlus CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb
  CFSG.KS.U43Mod CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.EvenSporadicStandard.M24Std.CU43 CertificateChecks.KernelU43B CFSG.Quasithin.H13.U43
  CertificateChecks.KernelU43Mod CFSG.Sporadic.SmallOddCore Subgroup

section Generic

variable {G G' : Type*} [Group G] [Group G']

theorem comm_of_bot {A B : Subgroup G} (hc : ⁅A, B⁆ = ⊥) {a b : G} (ha : a ∈ A) (hb : b ∈ B) :
    b * a = a * b :=
  mem_centralizer_iff.1 ((commutator_eq_bot_iff_le_centralizer.1 hc) ha) b hb

theorem plus_map (f : G →* G') (hf : Function.Injective f) {Q₁ Q₂ : Subgroup G}
    (h₁ : Nonempty (↥Q₁ ≃* QuaternionGroup 2)) (h₂ : Nonempty (↥Q₂ ≃* QuaternionGroup 2))
    (hc : ⁅Q₁, Q₂⁆ = ⊥) (hcard : Nat.card ↥(Q₁ ⊔ Q₂) = 32) :
    Nonempty (↥(Q₁.map f) ≃* QuaternionGroup 2) ∧ Nonempty (↥(Q₂.map f) ≃* QuaternionGroup 2) ∧
      ⁅Q₁.map f, Q₂.map f⁆ = ⊥ ∧ Nat.card ↥(Q₁.map f ⊔ Q₂.map f) = 32 := by
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  refine ⟨⟨(equivMapOfInjective Q₁ f hf).symm.trans e₁⟩,
    ⟨(equivMapOfInjective Q₂ f hf).symm.trans e₂⟩, ?_, ?_⟩
  · rw [← map_commutator, hc, Subgroup.map_bot]
  · rw [← Subgroup.map_sup,← Nat.card_congr (equivMapOfInjective (Q₁ ⊔ Q₂) f hf).toEquiv]
    exact hcard

theorem exists_common {Q₁ Q₂ : Subgroup G} (e₁ : Q₁ ≃* QuaternionGroup 2)
    (e₂ : Q₂ ≃* QuaternionGroup 2) (hc : ⁅Q₁, Q₂⁆ = ⊥) (hcard : Nat.card ↥(Q₁ ⊔ Q₂) = 32) :
    ∃ w, w ∈ Q₁ ∧ w ∈ Q₂ ∧ w ≠ 1 ∧ w * w = 1 := by
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
  have hq : QuaternionGroup.a 1 * QuaternionGroup.a 1 ≠ (1 : QuaternionGroup 2) := by decide
  have hy1 := sq_ne_one_of_equiv_symm e₁ hq
  have hyK := (e₁.symm (QuaternionGroup.a 1)).2
  have hwy := central_eq_sq e₁ hw1 (fun u hu => comm_of_bot hc hu hw2) hw hyK hy1
  refine ⟨w, hw1, hw2, hw, ?_⟩
  rw [hwy]
  exact fourth_eq_one e₁ hyK

theorem map_conj_le {K H : Subgroup G} {x : G} (hx : x ∈ H) (hK : K ≤ H) :
    K.map (MulAut.conj x).toMonoidHom ≤ H := by
  rintro _ ⟨q, hq, rfl⟩
  exact H.mul_mem (H.mul_mem hx (hK hq)) (H.inv_mem hx)

theorem map_conj_mul (K : Subgroup G) (a b : G) :
    (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      K.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem map_conj_hom (f : G →* G') (K : Subgroup G) (g : G) :
    (K.map (MulAut.conj g).toMonoidHom).map f = (K.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

theorem map_conj_inv {M N : Subgroup G} {x : G} (h : M.map (MulAut.conj x).toMonoidHom = N) :
    M = N.map (MulAut.conj x⁻¹).toMonoidHom := by
  rw [← h, map_conj_mul, inv_mul_cancel]
  ext z
  constructor
  · intro hz
    exact mem_map.2 ⟨z, hz, by simp [MulAut.conj_apply]⟩
  · intro hz
    obtain ⟨w, hw, e⟩ := mem_map.1 hz
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_one, one_mul, mul_one] at e
    rwa [← e]

end Generic


theorem exists_conj_le_S1 {R : Subgroup (Equiv.Perm (Fin 820))} (hR2 : IsPGroup 2 R)
    (hRle : R ≤ H4) : ∃ c : H4, R.map (MulAut.conj ((c : Equiv.Perm (Fin 820))⁻¹)).toMonoidHom ≤ S1 := by
  have hSC : Nat.card (S1.subgroupOf H4) = 128 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S1_le_H4).toEquiv, card_S1]
  have hfacC : (Nat.card H4).factorization 2 = 7 := by
    rw [show Nat.card H4 = 2 ^ 7 * 9 by rw [card_H4]; norm_num]
    rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 9)]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 H4 := Sylow.ofCard (S1.subgroupOf H4) (by rw [hSC, hfacC]; norm_num)
  have hR2C : IsPGroup 2 (R.subgroupOf H4) :=
    hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRle).symm
  obtain ⟨Q, hRQ⟩ := hR2C.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H4 S Q
  have hQmap : (Q : Subgroup H4) = (S : Subgroup H4).map (MulAut.conj c).toMonoidHom := by
    rw [← hc, Sylow.coe_subgroup_smul]
    rfl
  have hRQ' : R.subgroupOf H4 ≤ (S : Subgroup H4).map (MulAut.conj c).toMonoidHom := by
    rw [← hQmap]
    exact hRQ
  refine ⟨c, ?_⟩
  intro x hx
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 hx
  let rC : R.subgroupOf H4 := ⟨⟨r, hRle hr⟩, by
    rw [Subgroup.mem_subgroupOf]
    exact hr⟩
  have hrC : (rC : H4) ∈ (S : Subgroup H4).map (MulAut.conj c).toMonoidHom := hRQ' rC.2
  obtain ⟨p, hpP, hp⟩ := Subgroup.mem_map.1 hrC
  have hpval : (p : H4).val ∈ S1 := (Subgroup.mem_subgroupOf).1 hpP
  have hp' : (rC : H4) = MulAut.conj c p := hp.symm
  have hconj : (MulAut.conj ((c : Equiv.Perm (Fin 820))⁻¹)) r = (p : H4).val := by
    have e1 : r = (c : Equiv.Perm (Fin 820)) * p * (c : Equiv.Perm (Fin 820))⁻¹ :=
      congrArg Subtype.val hp'
    rw [MulAut.conj_apply, e1]
    group
  change (MulAut.conj ((c : Equiv.Perm (Fin 820))⁻¹)) r ∈ S1
  rw [hconj]
  exact hpval

theorem plus_conj_Q0 {Q₁ Q₂ : Subgroup (Equiv.Perm (Fin 820))} (hP : Q₁ ⊔ Q₂ ≤ P)
    (h₁ : Nonempty (↥Q₁ ≃* QuaternionGroup 2)) (h₂ : Nonempty (↥Q₂ ≃* QuaternionGroup 2))
    (hc : ⁅Q₁, Q₂⁆ = ⊥) (hcard : Nat.card ↥(Q₁ ⊔ Q₂) = 32) :
    ∃ x ∈ P, (Q₁ ⊔ Q₂).map (MulAut.conj x).toMonoidHom = Q0 := by
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  obtain ⟨w, hw1, hw2, hw, hww⟩ := exists_common e₁ e₂ hc hcard
  obtain ⟨y, hy, hyw⟩ := mem_conjClass.1 (invol_mem_classA (hP (mem_sup_left hw1)) hww hw)
  let f₁ := (MulAut.conj y⁻¹).toMonoidHom
  obtain ⟨hR₁, hR₂, hRc, hRcard⟩ := plus_map f₁ (MulAut.conj y⁻¹).injective ⟨e₁⟩ ⟨e₂⟩ hc hcard
  have hfw : f₁ w = CP 0 := by
    change (MulAut.conj y⁻¹) w = CP 0
    rw [MulAut.conj_apply, hyw]
    group
  have ha₁ : CP 0 ∈ Q₁.map f₁ := mem_map.2 ⟨w, hw1, hfw⟩
  have ha₂ : CP 0 ∈ Q₂.map f₁ := mem_map.2 ⟨w, hw2, hfw⟩
  have hRP : Q₁.map f₁ ⊔ Q₂.map f₁ ≤ P := by
    rw [← Subgroup.map_sup]
    exact map_conj_le (P.inv_mem hy) hP
  have hRH : Q₁.map f₁ ⊔ Q₂.map f₁ ≤ H4 := by
    refine sup_le (fun r hr => ?_) (fun r hr => ?_)
    · exact mem_H4 (hRP (mem_sup_left hr)) (comm_of_bot hRc hr ha₂).symm
    · exact mem_H4 (hRP (mem_sup_right hr)) (comm_of_bot hRc ha₁ hr)
  have hR2 : IsPGroup 2 ↥(Q₁.map f₁ ⊔ Q₂.map f₁) :=
    IsPGroup.of_card (n := 5) (by rw [hRcard]; norm_num)
  obtain ⟨c, hcS⟩ := exists_conj_le_S1 hR2 hRH
  let f₂ := (MulAut.conj ((c : Equiv.Perm (Fin 820))⁻¹)).toMonoidHom
  obtain ⟨hT₁, hT₂, hTc, hTcard⟩ :=
    plus_map f₂ (MulAut.conj ((c : Equiv.Perm (Fin 820))⁻¹)).injective hR₁ hR₂ hRc hRcard
  have hfa : f₂ (CP 0) = CP 0 := by
    change (MulAut.conj ((c : Equiv.Perm (Fin 820))⁻¹)) (CP 0) = CP 0
    rw [MulAut.conj_apply, inv_inv, mul_assoc, ← comm_of_mem_H4 c.2]
    group
  have hb₁ : CP 0 ∈ (Q₁.map f₁).map f₂ := mem_map.2 ⟨CP 0, ha₁, hfa⟩
  have hb₂ : CP 0 ∈ (Q₂.map f₁).map f₂ := mem_map.2 ⟨CP 0, ha₂, hfa⟩
  have hTS : (Q₁.map f₁).map f₂ ⊔ (Q₂.map f₁).map f₂ ≤ S1 := by
    rw [← Subgroup.map_sup]
    exact hcS
  obtain ⟨e₁'⟩ := hT₁
  obtain ⟨e₂'⟩ := hT₂
  have hQ0 := plus_eq_Q0 e₁' e₂' hTc hTcard hTS hb₁ hb₂
  refine ⟨(c : Equiv.Perm (Fin 820))⁻¹ * y⁻¹, P.mul_mem (P.inv_mem (H4_le_P c.2)) (P.inv_mem hy),
    ?_⟩
  rw [← map_conj_mul, ← hQ0, ← Subgroup.map_sup, ← Subgroup.map_sup]

theorem cent_plus_perm {Q₁ Q₂ : Subgroup (Equiv.Perm (Fin 820))} (hP : Q₁ ⊔ Q₂ ≤ P)
    (h₁ : Nonempty (↥Q₁ ≃* QuaternionGroup 2)) (h₂ : Nonempty (↥Q₂ ≃* QuaternionGroup 2))
    (hc : ⁅Q₁, Q₂⁆ = ⊥) (hcard : Nat.card ↥(Q₁ ⊔ Q₂) = 32) {g : Equiv.Perm (Fin 820)}
    (hg : g ∈ P) (hcg : ∀ q ∈ Q₁ ⊔ Q₂, g * q = q * g) : g ∈ Q₁ ⊔ Q₂ := by
  obtain ⟨x, hx, hQ⟩ := plus_conj_Q0 hP h₁ h₂ hc hcard
  have hg' : x * g * x⁻¹ ∈ Q0 := by
    have hcj : ∀ j < 32, x * g * x⁻¹ * QP j = QP j * (x * g * x⁻¹) := by
      intro j hj
      have hj' : QP j ∈ (Q₁ ⊔ Q₂).map (MulAut.conj x).toMonoidHom := hQ ▸ QP_mem_Q0 hj
      obtain ⟨q, hq, e⟩ := mem_map.1 hj'
      have e' : QP j = x * q * x⁻¹ := e.symm
      rw [e']
      calc x * g * x⁻¹ * (x * q * x⁻¹) = x * (g * q) * x⁻¹ := by group
        _ = x * (q * g) * x⁻¹ := by rw [hcg q hq]
        _ = x * q * x⁻¹ * (x * g * x⁻¹) := by group
    rcases cent_Q0 (P.mul_mem (P.mul_mem hx hg) (P.inv_mem hx)) hcj with e | e
    · rw [e]
      exact Q0.one_mem
    · rw [e]
      exact a_mem_Q0
  rw [← hQ] at hg'
  obtain ⟨q, hq, e⟩ := mem_map.1 hg'
  have e' : x * q * x⁻¹ = x * g * x⁻¹ := e
  have hqg : q = g := mul_left_cancel (mul_right_cancel e')
  rwa [← hqg]

open CFSG.LieType.Multipliers.U43 (X₀ psi_injective)

local notation "ψ₀" => CFSG.LieType.Multipliers.U43.psi

theorem range_le_P {K : Subgroup X₀} : K.map ψ₀ ≤ P := by
  rw [P_eq_range]
  exact map_le_range ψ₀ K

theorem x0_cent (Q₁ Q₂ : Subgroup X₀) (h₁ : Nonempty (↥Q₁ ≃* QuaternionGroup 2))
    (h₂ : Nonempty (↥Q₂ ≃* QuaternionGroup 2)) (hc : ⁅Q₁, Q₂⁆ = ⊥)
    (hcard : Nat.card ↥(Q₁ ⊔ Q₂) = 32) :
    centralizer ((Q₁ ⊔ Q₂ : Subgroup X₀) : Set X₀) ≤ Q₁ ⊔ Q₂ := by
  obtain ⟨h₁', h₂', hc', hcard'⟩ := plus_map ψ₀ psi_injective h₁ h₂ hc hcard
  have hP : Q₁.map ψ₀ ⊔ Q₂.map ψ₀ ≤ P := by
    rw [← Subgroup.map_sup]
    exact range_le_P
  intro y hy
  have hyP : ψ₀ y ∈ P := by
    rw [P_eq_range]
    exact ⟨y, rfl⟩
  have hm := cent_plus_perm hP h₁' h₂' hc' hcard' hyP (fun q hq => by
    rw [← Subgroup.map_sup] at hq
    obtain ⟨q', hq', e⟩ := mem_map.1 hq
    rw [← e, ← map_mul, ← map_mul, mem_centralizer_iff.1 hy q' hq'])
  rw [← Subgroup.map_sup] at hm
  exact (mem_map_iff_mem psi_injective).1 hm

theorem x0_conj (Q₁ Q₂ Q₃ Q₄ : Subgroup X₀) (h₁ : Nonempty (↥Q₁ ≃* QuaternionGroup 2))
    (h₂ : Nonempty (↥Q₂ ≃* QuaternionGroup 2)) (hc : ⁅Q₁, Q₂⁆ = ⊥)
    (hcard : Nat.card ↥(Q₁ ⊔ Q₂) = 32) (h₃ : Nonempty (↥Q₃ ≃* QuaternionGroup 2))
    (h₄ : Nonempty (↥Q₄ ≃* QuaternionGroup 2)) (hc' : ⁅Q₃, Q₄⁆ = ⊥)
    (hcard' : Nat.card ↥(Q₃ ⊔ Q₄) = 32) :
    ∃ g : X₀, Q₃ ⊔ Q₄ = (Q₁ ⊔ Q₂).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨k₁, k₂, kc, kcard⟩ := plus_map ψ₀ psi_injective h₁ h₂ hc hcard
  obtain ⟨k₃, k₄, kc', kcard'⟩ := plus_map ψ₀ psi_injective h₃ h₄ hc' hcard'
  have hP : Q₁.map ψ₀ ⊔ Q₂.map ψ₀ ≤ P := by
    rw [← Subgroup.map_sup]
    exact range_le_P
  have hP' : Q₃.map ψ₀ ⊔ Q₄.map ψ₀ ≤ P := by
    rw [← Subgroup.map_sup]
    exact range_le_P
  obtain ⟨x, hx, hQ⟩ := plus_conj_Q0 hP k₁ k₂ kc kcard
  obtain ⟨x', hx', hQ'⟩ := plus_conj_Q0 hP' k₃ k₄ kc' kcard'
  rw [← Subgroup.map_sup] at hQ hQ'
  have hz : x'⁻¹ * x ∈ MonoidHom.range ψ₀ := by
    rw [← P_eq_range]
    exact P.mul_mem (P.inv_mem hx') hx
  obtain ⟨g, hg⟩ := hz
  refine ⟨g, map_injective psi_injective ?_⟩
  rw [map_conj_hom, hg, ← map_conj_mul, hQ, map_conj_inv hQ']

end CertificateChecks.KernelU43CentPlus

end
