module

public import Certificates.Kernel.SporCovPerm.M24
public import CFSG.Certificates.Kernel.SporCov.PermKit
public import CFSG.Certificates.Kernel.SporCov.PCl
public import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.KD.SporCovPerm.M24

open CFSG.KC.SporCov CFSG.KD.SporCov CFSG.StandardType.SporadicShape CFSG.Sporadic.Th
  CFSG.Blueprint CFSG.Sporadic.Mathieu

theorem hA : ∀ x < 24, nthN (nthW F.A 0) x = idx 24 m24a x := by decide +kernel

theorem hAi : ∀ x < 24, nthN (nthW F.A 1) x = idx 24 m24a⁻¹ x :=
  inv_of_left hA (by decide +kernel)

theorem hB : ∀ x < 24, nthN (nthW F.A 2) x = idx 24 m24b x := by decide +kernel

theorem hBi : ∀ x < 24, nthN (nthW F.A 3) x = idx 24 m24b⁻¹ x :=
  inv_of_left hB (by decide +kernel)

theorem bs_eq : bs = List.range 24 := by decide +kernel

theorem model : Model letP E (wE (fP m24a m24b)) ∧
    ∀ u, chW letP u = true → wE (fP m24a m24b) u = 1 → E u [] = true := by
  unfold E
  rw [bs_eq]
  exact PermKit.model hA hAi hB hBi

theorem factorization_three : (244823040 : ℕ).factorization 3 = 3 := by
  rw [Nat.factorization_def _ Nat.prime_three]
  have h : padicValNat 3 9067520 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [show (244823040 : ℕ) = 3 * (3 * (3 * 9067520)) by norm_num,
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num), h]

theorem sporKRestCover_three :
    SporKRestCover 3 ↥NativeSporadic.M24 := by
  obtain ⟨hM, hc⟩ := model
  exact hM.cover_of_p3c Nat.prime_three (by rw [card_M24, factorization_three]) hc Ck.ok
    fun _ => PermKit.top_of_seeds m24_eq rfl rfl

end CFSG.KD.SporCovPerm.M24

end
