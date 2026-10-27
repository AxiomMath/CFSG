module

public import Certificates.Kernel.SporCovPerm.M12
public import CFSG.Certificates.Kernel.SporCov.PermKit
public import CFSG.Certificates.Kernel.SporCov.PCl
public import CFSG.Sporadic.Mathieu.M12

public section

namespace CFSG.KD.SporCovPerm.M12

open CFSG.KC.SporCov CFSG.KD.SporCov CFSG.StandardType.SporadicShape CFSG.Sporadic.Th
  CFSG.Blueprint CFSG.Sporadic.Mathieu

theorem hA : ∀ x < 12, nthN (nthW F.A 0) x = idx 12 m12a x := by decide +kernel

theorem hAi : ∀ x < 12, nthN (nthW F.A 1) x = idx 12 m12a⁻¹ x :=
  inv_of_left hA (by decide +kernel)

theorem hB : ∀ x < 12, nthN (nthW F.A 2) x = idx 12 m12b x := by decide +kernel

theorem hBi : ∀ x < 12, nthN (nthW F.A 3) x = idx 12 m12b⁻¹ x :=
  inv_of_left hB (by decide +kernel)

theorem bs_eq : bs = List.range 12 := by decide +kernel

theorem model : Model letP E (wE (fP m12a m12b)) ∧
    ∀ u, chW letP u = true → wE (fP m12a m12b) u = 1 → E u [] = true := by
  unfold E
  rw [bs_eq]
  exact PermKit.model hA hAi hB hBi

theorem factorization_three : (95040 : ℕ).factorization 3 = 3 := by
  rw [Nat.factorization_def _ Nat.prime_three]
  have h : padicValNat 3 3520 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [show (95040 : ℕ) = 3 * (3 * (3 * 3520)) by norm_num,
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num), h]

theorem sporKRestCover_three :
    SporKRestCover 3 ↥NativeSporadic.M12 := by
  obtain ⟨hM, hc⟩ := model
  exact hM.cover_of_p3c Nat.prime_three (by rw [card_M12, factorization_three]) hc Ck.ok
    fun _ => PermKit.top_of_seeds m12_eq rfl rfl

end CFSG.KD.SporCovPerm.M12

end
