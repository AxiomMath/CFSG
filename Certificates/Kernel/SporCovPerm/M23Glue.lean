module

public import Certificates.Kernel.SporCovPerm.M23
public import CFSG.Certificates.Kernel.SporCov.PermKit
public import CFSG.Certificates.Kernel.SporCov.PCl
public import CFSG.Sporadic.Mathieu.M23

public section

namespace CFSG.KD.SporCovPerm.M23

open CFSG.KC.SporCov CFSG.KD.SporCov CFSG.StandardType.SporadicShape CFSG.Sporadic.Th
  CFSG.Blueprint CFSG.Sporadic.Mathieu Equiv

abbrev gA : Perm (Fin 23) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
    List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
    List.formPerm [20, 21]

abbrev gB : Perm (Fin 23) :=
  List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
    List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]

theorem m23_eq : NativeSporadic.M23 = Subgroup.closure {gA, gB} := rfl

abbrev a : NativeSporadic.M23 := ⟨gA, PermKit.a_mem m23_eq⟩

abbrev b : NativeSporadic.M23 := ⟨gB, PermKit.b_mem m23_eq⟩

theorem hA : ∀ x < 23, nthN (nthW F.A 0) x = idx 23 a x := by decide +kernel

theorem hAi : ∀ x < 23, nthN (nthW F.A 1) x = idx 23 a⁻¹ x :=
  inv_of_left hA (by decide +kernel)

theorem hB : ∀ x < 23, nthN (nthW F.A 2) x = idx 23 b x := by decide +kernel

theorem hBi : ∀ x < 23, nthN (nthW F.A 3) x = idx 23 b⁻¹ x :=
  inv_of_left hB (by decide +kernel)

theorem bs_eq : bs = List.range 23 := by decide +kernel

theorem model : Model letP E (wE (fP a b)) ∧
    ∀ u, chW letP u = true → wE (fP a b) u = 1 → E u [] = true := by
  unfold E
  rw [bs_eq]
  exact PermKit.model hA hAi hB hBi

theorem factorization_three : (10200960 : ℕ).factorization 3 = 2 := by
  rw [Nat.factorization_def _ Nat.prime_three]
  have h : padicValNat 3 1133440 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [show (10200960 : ℕ) = 3 * (3 * 1133440) by norm_num,
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num), h]

theorem sporKRestCover_three :
    SporKRestCover 3 ↥NativeSporadic.M23 := by
  have hcard : Nat.card ↥NativeSporadic.M23 = 10200960 := by
    rw [nativeM23_eq, ← CFSG.M23.M23Group.card_M23]
    exact Nat.card_eq_fintype_card
  obtain ⟨hM, hc⟩ := model
  have hk := Ck.ok
  unfold chk at hk
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨⟨⟨hpcl, o₁⟩, o₂⟩, hcm⟩, h₁⟩, h₂⟩, hT⟩, hne⟩ := hk
  have hR : P3Rel 3 (wE (fP a b) F.G1) (wE (fP a b) F.G2) 1 :=
    ⟨one_pow 3, by rw [one_mul, mul_one], by rw [one_mul, mul_one],
      by rw [one_mul]; exact hM.comm o₁ o₂ hcm, ⟨0, by rw [pow_zero]; exact hM.pow o₁ h₁⟩,
      ⟨0, by rw [pow_zero]; exact hM.pow o₂ h₂⟩⟩
  obtain ⟨ot, hgen⟩ := hM.generating_of_pclOK Nat.prime_three hR.isPGroup o₁ o₂ hpcl
    fun _ => PermKit.top_of_seeds m23_eq rfl rfl
  exact hM.cover_of_val_two Nat.prime_three (by rw [hcard, factorization_three]) hc ot hne hT hgen

end CFSG.KD.SporCovPerm.M23

end
