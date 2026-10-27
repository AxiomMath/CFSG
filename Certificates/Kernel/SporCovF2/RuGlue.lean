module

public import Certificates.Kernel.SporCovF2.Ru
public import CFSG.Certificates.Kernel.SporCov.F2Kit
public import CFSG.Certificates.Kernel.SporCov.PCl
public import CFSG.Sporadic.Bridge.RuSurjBase

public section

namespace CFSG.KD.SporCovF2.Ru

open CFSG.KC.SporCov CFSG.KD.SporCov CFSG.StandardType.SporadicShape CFSG.Sporadic.SmallF2
open CFSG.Sporadic.Ru.Native (ruData)

theorem factorization_three : (145926144000 : ℕ).factorization 3 = 3 := by
  rw [Nat.factorization_def _ Nat.prime_three]
  have h : padicValNat 3 5404672000 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [show (145926144000 : ℕ) = 3 * (3 * (3 * 5404672000)) by norm_num,
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num), h]

theorem factorization_five : (145926144000 : ℕ).factorization 5 = 3 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [Nat.factorization_def _ Nat.prime_five]
  have h : padicValNat 5 1167409152 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [show (145926144000 : ℕ) = 5 * (5 * (5 * 1167409152)) by norm_num,
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num), h]

theorem top_of_seeds {R : List (List ℕ)} (e0 : nthW R 0 = [0]) (e1 : nthW R 1 = [2])
    (T : Subgroup ↥(J ruData)) (h : ∀ k, wE (fF (a ruData) (b ruData)) (nthW R k) ∈ T) : T = ⊤ := by
  have h0 := h 0
  have h1 := h 1
  rw [e0, wE_cons, wE_nil, one_mul, fF_zero] at h0
  rw [e1, wE_cons, wE_nil, one_mul, fF_two] at h1
  rw [eq_top_iff, ← closure_ab ruData, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact h0
  · exact h1

theorem sporKRestCover_three_J : SporKRestCover 3 ↥(J ruData) := by
  obtain ⟨E, hk, hM, hc⟩ := kitF_J (ruData ()) CertificateChecks.KernelVec.Ru.hA
    CertificateChecks.KernelVec.Ru.hB Ck.bA Ck.bB Ck.ok3
  exact hM.cover_of_p3c Nat.prime_three
    (by rw [CFSG.Sporadic.Bridge.Ru.card_J, factorization_three]) hc hk (top_of_seeds rfl rfl)

theorem sporKRestCover_five_J : SporKRestCover 5 ↥(J ruData) := by
  obtain ⟨E, hk, hM, hc⟩ := kitF_J (ruData ()) CertificateChecks.KernelVec.Ru.hA
    CertificateChecks.KernelVec.Ru.hB Ck.bA Ck.bB Ck.ok5
  exact hM.cover_of_p3c Nat.prime_five
    (by rw [CFSG.Sporadic.Bridge.Ru.card_J, factorization_five]) hc hk (top_of_seeds rfl rfl)

end CFSG.KD.SporCovF2.Ru

end
