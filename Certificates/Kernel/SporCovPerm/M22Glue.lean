module

public import Certificates.Kernel.SporCovPerm.M22
public import CFSG.Certificates.Kernel.SporCov.PermKit
public import CFSG.Certificates.Kernel.SporCov.PCl
public import CFSG.Sporadic.Mathieu.M22

public section

namespace CFSG.KD.SporCovPerm.M22

open CFSG.KC.SporCov CFSG.KD.SporCov CFSG.StandardType.SporadicShape CFSG.Sporadic.Th
  CFSG.Blueprint CFSG.Sporadic.Mathieu

theorem hA : ∀ x < 22, nthN (nthW F.A 0) x = idx 22 m22a x := by decide +kernel

theorem hAi : ∀ x < 22, nthN (nthW F.A 1) x = idx 22 m22a⁻¹ x :=
  inv_of_left hA (by decide +kernel)

theorem hB : ∀ x < 22, nthN (nthW F.A 2) x = idx 22 m22b x := by decide +kernel

theorem hBi : ∀ x < 22, nthN (nthW F.A 3) x = idx 22 m22b⁻¹ x :=
  inv_of_left hB (by decide +kernel)

theorem bs_eq : bs = List.range 22 := by decide +kernel

theorem model : Model letP E (wE (fP m22a m22b)) ∧
    ∀ u, chW letP u = true → wE (fP m22a m22b) u = 1 → E u [] = true := by
  unfold E
  rw [bs_eq]
  exact PermKit.model hA hAi hB hBi

theorem factorization_three : (443520 : ℕ).factorization 3 = 2 := by
  rw [Nat.factorization_def _ Nat.prime_three]
  have h : padicValNat 3 49280 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [show (443520 : ℕ) = 3 * (3 * 49280) by norm_num,
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num), h]

theorem sporKRestCover_three :
    SporKRestCover 3 ↥NativeSporadic.M22 := by
  obtain ⟨hM, hc⟩ := model
  have hk := Ck.ok
  unfold chk at hk
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨⟨⟨hpcl, o₁⟩, o₂⟩, hcm⟩, h₁⟩, h₂⟩, hT⟩, hne⟩ := hk
  have hR : P3Rel 3 (wE (fP m22a m22b) F.G1) (wE (fP m22a m22b) F.G2) 1 :=
    ⟨one_pow 3, by rw [one_mul, mul_one], by rw [one_mul, mul_one],
      by rw [one_mul]; exact hM.comm o₁ o₂ hcm, ⟨0, by rw [pow_zero]; exact hM.pow o₁ h₁⟩,
      ⟨0, by rw [pow_zero]; exact hM.pow o₂ h₂⟩⟩
  obtain ⟨ot, hgen⟩ := hM.generating_of_pclOK Nat.prime_three hR.isPGroup o₁ o₂ hpcl
    fun _ => PermKit.top_of_seeds m22_eq rfl rfl
  exact hM.cover_of_val_two Nat.prime_three (by rw [card_M22, factorization_three]) hc ot hne hT
    hgen

end CFSG.KD.SporCovPerm.M22

end
