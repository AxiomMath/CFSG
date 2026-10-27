module

public import Certificates.Kernel.SporCovF2.Co3
public import CFSG.Certificates.Kernel.SporCov.F2Kit
public import CFSG.Certificates.Kernel.SporCov.PCl
public import CFSG.Sporadic.Bridge.Co3Surj

public section

namespace CFSG.KD.SporCovF2.Co3

open CFSG.KC.SporCov CFSG.KD.SporCov CFSG.StandardType.SporadicShape CFSG.Sporadic.SmallF2
open CFSG.Sporadic.Co3.Native (co3Data)

theorem factorization_five : (495766656000 : ℕ).factorization 5 = 3 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [Nat.factorization_def _ Nat.prime_five]
  have e : (495766656000 : ℕ) = 5 ^ 3 * 3966133248 := by norm_num
  rw [e, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 3966133248), add_zero]

theorem top_of_seeds {R : List (List ℕ)} (e0 : nthW R 0 = [0]) (e1 : nthW R 1 = [2])
    (T : Subgroup ↥(J co3Data)) (h : ∀ k, wE (fF (a co3Data) (b co3Data)) (nthW R k) ∈ T) :
    T = ⊤ := by
  have h0 := h 0
  have h1 := h 1
  rw [e0, wE_cons, wE_nil, one_mul, fF_zero] at h0
  rw [e1, wE_cons, wE_nil, one_mul, fF_two] at h1
  rw [eq_top_iff, ← closure_ab co3Data, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact h0
  · exact h1

theorem sporKRestCover_five_J :
    SporKRestCover 5 ↥(J co3Data) := by
  obtain ⟨E, hk, hM, hc⟩ := kitF_J (co3Data ()) CertificateChecks.KernelVec.Co3.hA
    CertificateChecks.KernelVec.Co3.hB Ck.bA Ck.bB Ck.ok
  exact hM.cover_of_p3l Nat.prime_five
    (by rw [CFSG.Sporadic.Bridge.Co3.card_J, factorization_five]) hc hk (top_of_seeds rfl rfl)

end CFSG.KD.SporCovF2.Co3

end
