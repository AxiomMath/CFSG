module

public import Certificates.Kernel.U43CentPlus.Class
public import Certificates.Kernel.U43CentPlus.Cent
public import Certificates.Kernel.U43CentPlus.Q8

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43CentPlus

open CFSG.KC.Enum CFSG.KC.U43Mod CFSG.KC.U43CentPlus CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb
  CFSG.KS.U43Mod CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.EvenSporadicStandard.M24Std.CU43 CertificateChecks.KernelU43B CFSG.Quasithin.H13.U43
  CertificateChecks.KernelU43Mod Subgroup

theorem q8_sq_one : ∀ x y : QuaternionGroup 2, x * x = 1 → y * y ≠ 1 → x = 1 ∨ x = y * y := by
  decide

theorem le_of_roots {G : Type*} [Group G] {K H : Subgroup G} (e : K ≃* QuaternionGroup 2)
    (h : ∀ g ∈ K, g * g ≠ 1 → g ∈ H) : K ≤ H := by
  intro x hx
  by_cases hx1 : x * x = 1
  · have hq : QuaternionGroup.a 1 * QuaternionGroup.a 1 ≠ (1 : QuaternionGroup 2) := by decide
    have hy1 := sq_ne_one_of_equiv_symm e hq
    have hyK := (e.symm (QuaternionGroup.a 1)).2
    have hxx : (⟨x, hx⟩ : K) * ⟨x, hx⟩ = 1 := Subtype.ext hx1
    have hx1' : e ⟨x, hx⟩ * e ⟨x, hx⟩ = 1 := by
      rw [← map_mul, hxx, map_one]
    rcases q8_sq_one _ _ hx1' hq with h1 | h1
    · have e1 : (⟨x, hx⟩ : K) = 1 := (MulEquiv.map_eq_one_iff e).1 h1
      have e2 : x = 1 := congrArg Subtype.val e1
      rw [e2]
      exact H.one_mem
    · have e1 : (⟨x, hx⟩ : K) = e.symm (QuaternionGroup.a 1) * e.symm (QuaternionGroup.a 1) := by
        rw [← map_mul, ← h1, MulEquiv.symm_apply_apply]
      have e2 : x = ((e.symm (QuaternionGroup.a 1) : K) : G) * (e.symm (QuaternionGroup.a 1) : K) :=
        congrArg Subtype.val e1
      rw [e2]
      exact H.mul_mem (h _ hyK hy1) (h _ hyK hy1)
  · exact h x hx hx1


theorem CE_mem_Q0 {c : ℕ} (hc : c < 32) : CE c ∈ Q0 := by
  have e1 : Nat.mod c 32 = c := by
    change c % 32 = c
    omega
  have e2 : Nat.div c 32 = 0 := by
    change c / 32 = 0
    omega
  rw [CE, e1, e2, TP_zero, mul_one]
  exact QP_mem_Q0 hc

theorem mem_Q0_of_plus {Q₁ Q₂ : Subgroup (Equiv.Perm (Fin 820))}
    (e₁ : Q₁ ≃* QuaternionGroup 2) (e₂ : Q₂ ≃* QuaternionGroup 2) (hc : ⁅Q₁, Q₂⁆ = ⊥)
    (hcard : Nat.card ↥(Q₁ ⊔ Q₂) = 32) (hle : Q₁ ⊔ Q₂ ≤ S1) (ha : CP 0 ∈ Q₁)
    {g : Equiv.Perm (Fin 820)} (hg : g ∈ Q₁) (hg1 : g * g ≠ 1) : g ∈ Q0 := by
  have hsq : g * g = CP 0 :=
    (central_eq_sq e₁ ha (fun u hu => (comm_of_mem_H4 (S1_le_H4 (hle (mem_sup_left hu)))).symm)
      CP0_ne hg hg1).symm
  obtain ⟨c, hc128, rfl⟩ := mem_S1_iff.1 (hle (mem_sup_left hg))
  by_cases h32 : c < 32
  · exact CE_mem_Q0 h32
  · exfalso
    have h4 := ncard_Rt_CE (by omega) hc128 hsq
    have h8 := eight_roots e₁ e₂ hc hcard hg hg1
    have hsub : {h | h ∈ Q₁ ⊔ Q₂ ∧ h * CE c = CE c * h ∧ h * h = CE c * CE c} ⊆ Rt (CE c) :=
      fun h hh => ⟨S1_le_H4 (hle hh.1), hh.2.1, hh.2.2.trans hsq⟩
    have h48 := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega

theorem plus_eq_Q0 {Q₁ Q₂ : Subgroup (Equiv.Perm (Fin 820))}
    (e₁ : Q₁ ≃* QuaternionGroup 2) (e₂ : Q₂ ≃* QuaternionGroup 2) (hc : ⁅Q₁, Q₂⁆ = ⊥)
    (hcard : Nat.card ↥(Q₁ ⊔ Q₂) = 32) (hle : Q₁ ⊔ Q₂ ≤ S1) (ha₁ : CP 0 ∈ Q₁)
    (ha₂ : CP 0 ∈ Q₂) : Q₁ ⊔ Q₂ = Q0 := by
  have h1 : Q₁ ≤ Q0 := le_of_roots e₁ fun g hg hg1 =>
    mem_Q0_of_plus e₁ e₂ hc hcard hle ha₁ hg hg1
  have hc' : ⁅Q₂, Q₁⁆ = ⊥ := by
    rw [commutator_comm]
    exact hc
  have hcard' : Nat.card ↥(Q₂ ⊔ Q₁) = 32 := by
    rw [sup_comm]
    exact hcard
  have hle' : Q₂ ⊔ Q₁ ≤ S1 := by
    rw [sup_comm]
    exact hle
  have h2 : Q₂ ≤ Q0 := le_of_roots e₂ fun g hg hg1 =>
    mem_Q0_of_plus e₂ e₁ hc' hcard' hle' ha₂ hg hg1
  exact Subgroup.eq_of_le_of_card_ge (sup_le h1 h2) (by rw [card_Q0, hcard])

end CertificateChecks.KernelU43CentPlus

end
