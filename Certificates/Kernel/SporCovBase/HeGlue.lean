module

public import Certificates.Kernel.SporCovBase.He
public import CFSG.Certificates.Kernel.SporCov.BaseKit
public import CFSG.Certificates.Kernel.SporCov.PCl
public import Certificates.Kernel.He27143.Final
public import CFSG.Sporadic.He.Simple

public section

namespace CFSG.KD.SporCovBase.He

open CFSG.KC.SporCov CFSG.KD.SporCov CFSG.StandardType.SporadicShape CFSG.Sporadic.Th
  CFSG.KS.PEnum
open CFSG.Sporadic.He (J a b)


theorem hA : ∀ x < 8330, r32 CFSG.KD.HeOrb.AL x = idx 8330 a x := fun x hx => by
  have h := CFSG.Sporadic.He.rep_alpha x hx
  unfold CFSG.Sporadic.He.orb at h
  rwa [CFSG.KD.HeOrb.orbitData_eq, CFSG.KD.HeOrb.alpha_ap hx] at h

theorem hB : ∀ x < 8330, r32 CFSG.KD.HeOrb.BE x = idx 8330 b x := fun x hx => by
  have h := CFSG.Sporadic.He.rep_beta x hx
  unfold CFSG.Sporadic.He.orb at h
  rwa [CFSG.KD.HeOrb.orbitData_eq, CFSG.KD.HeOrb.beta_ap hx] at h

theorem hAi : ∀ x < 8330, r32 CFSG.KD.HeOrb.AL x = idx 8330 a⁻¹ x := by
  have e : a⁻¹ = a := inv_eq_of_mul_eq_one_right CFSG.Sporadic.He.a_mul_self
  rw [e]
  exact hA

theorem hBi : ∀ x < 8330, r32 CFSG.KD.HeTab.BI x = idx 8330 b⁻¹ x :=
  inv_of_left hB fun _ hx => (CFSG.KD.HeTab.inv_facts hx).2

theorem bs_lt : ∀ x ∈ bs, x < 8330 := by decide

theorem sep_bs (g : J) (h : ∀ x ∈ bs, idx 8330 g x = x) : g = 1 := by
  have hl : ∀ i ≤ 5, g ∈ CFSG.Sporadic.He.lvl i := by
    intro i hi
    induction i with
    | zero => exact CFSG.Sporadic.He.mem_lvl_zero g
    | succ i ih =>
      refine (CFSG.Sporadic.He.chain_facts'.2.1 i
        (by rw [CFSG.Sporadic.He.chainBase_size]; omega) g (ih (by omega))).1 (h _ ?_)
      have hi4 : i < 5 := by omega
      interval_cases i <;> decide
  have hc := CFSG.Sporadic.He.chain_facts'.2.2 5 (by rw [CFSG.Sporadic.He.chainBase_size])
  rw [CFSG.Sporadic.He.chainBase_size, Finset.Ico_self, Finset.prod_empty] at hc
  have hb := Subgroup.eq_bot_of_card_eq _ hc
  have hg := hl 5 le_rfl
  rw [hb] at hg
  exact (Subgroup.mem_bot).1 hg

theorem model : Model letP E (wE (fP a b)) ∧
    ∀ u, chW letP u = true → wE (fP a b) u = 1 → E u [] = true :=
  eqB_model hA hAi hB hBi bs_lt sep_bs

theorem factorization_three : (4030387200 : ℕ).factorization 3 = 3 := by
  rw [Nat.factorization_def _ Nat.prime_three]
  have h : padicValNat 3 149273600 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [show (4030387200 : ℕ) = 3 * (3 * (3 * 149273600)) by norm_num,
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num), h]

theorem factorization_five : (4030387200 : ℕ).factorization 5 = 2 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [Nat.factorization_def _ Nat.prime_five]
  have h : padicValNat 5 161215488 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [show (4030387200 : ℕ) = 5 * (5 * 161215488) by norm_num,
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num), h]

theorem factorization_seven : (4030387200 : ℕ).factorization 7 = 3 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [Nat.factorization_def _ (by norm_num : Nat.Prime 7)]
  have h : padicValNat 7 11750400 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [show (4030387200 : ℕ) = 7 * (7 * (7 * 11750400)) by norm_num,
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num), h]

theorem top_of_seeds {R : List (List ℕ)} (e0 : nthW R 0 = [0]) (e1 : nthW R 1 = [2])
    {T : Subgroup J} (h : ∀ k, wE (fP a b) (nthW R k) ∈ T) : T = ⊤ := by
  have h0 := h 0
  have h1 := h 1
  rw [e0, wE_cons, wE_nil, one_mul, fP_zero] at h0
  rw [e1, wE_cons, wE_nil, one_mul, fP_two] at h1
  rw [eq_top_iff, ← CFSG.Sporadic.He.closure_ab, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact h0
  · exact h1

theorem sporKRestCover_three_J : SporKRestCover 3 ↥J := by
  obtain ⟨hM, hc⟩ := model
  exact hM.cover_of_p3c Nat.prime_three
    (by rw [CFSG.Sporadic.He.card_J, factorization_three]) hc Ck.ok3 fun _ => top_of_seeds rfl rfl

theorem sporKRestCover_five_J : SporKRestCover 5 ↥J := by
  obtain ⟨hM, hc⟩ := model
  have hk := Ck.ok5
  unfold chk5 at hk
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨⟨⟨hpcl, o₁⟩, o₂⟩, hcm⟩, h₁⟩, h₂⟩, hT⟩, hne⟩ := hk
  have hR : P3Rel 5 (wE (fP a b) F5.G1) (wE (fP a b) F5.G2) 1 :=
    ⟨one_pow 5, by rw [one_mul, mul_one], by rw [one_mul, mul_one],
      by rw [one_mul]; exact hM.comm o₁ o₂ hcm, ⟨0, by rw [pow_zero]; exact hM.pow o₁ h₁⟩,
      ⟨0, by rw [pow_zero]; exact hM.pow o₂ h₂⟩⟩
  obtain ⟨ot, hgen⟩ := hM.generating_of_pclOK Nat.prime_five hR.isPGroup o₁ o₂ hpcl
    fun _ => top_of_seeds rfl rfl
  exact hM.cover_of_val_two Nat.prime_five
    (by rw [CFSG.Sporadic.He.card_J, factorization_five]) hc ot hne hT hgen

theorem sporKRestCover_seven_J : SporKRestCover 7 ↥J := by
  obtain ⟨hM, hc⟩ := model
  exact hM.cover_of_p3c (by norm_num)
    (by rw [CFSG.Sporadic.He.card_J, factorization_seven]) hc Ck.ok7 fun _ => top_of_seeds rfl rfl

end CFSG.KD.SporCovBase.He

end
