module

public import Certificates.Kernel.SporCovF2.HS
public import CFSG.Certificates.Kernel.SporCov.F2Kit
public import CFSG.Certificates.Kernel.SporCov.PCl
public import CFSG.Sporadic.Bridge.HSSurj

public section

namespace CFSG.KD.SporCovF2.HS

open CFSG.KC.SporCov CFSG.KD.SporCov CFSG.StandardType.SporadicShape CFSG.Sporadic.SmallF2
open CFSG.Sporadic.HS.Native (hsData)

theorem factorization_three : (44352000 : ℕ).factorization 3 = 2 := by
  rw [Nat.factorization_def _ Nat.prime_three]
  have h : padicValNat 3 4928000 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [show (44352000 : ℕ) = 3 * (3 * 4928000) by norm_num,
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num), h]

theorem sporKRestCover_three_J : SporKRestCover 3 ↥(J hsData) := by
  obtain ⟨E, hk, hM, hc⟩ := kitF_J (hsData ()) CertificateChecks.KernelVec.HS.hA
    CertificateChecks.KernelVec.HS.hB Ck.bA Ck.bB Ck.ok
  unfold chk at hk
  simp only [Bool.and_eq_true, allLt_iff] at hk
  obtain ⟨⟨⟨⟨⟨hH, hL⟩, hs⟩, hS⟩, hne⟩, ht⟩ := hk
  have hcard : Nat.card ↥(J hsData) = 44352000 := by
    rw [← Nat.card_congr CFSG.Sporadic.Bridge.HS.nativeEquiv.toEquiv, CFSG.Sporadic.HS.card_HS]
  have hMc : chA letL F.M = true := (hM.clH_facts hH ht).2.1
  have hR : ∀ k, wE (fF (a hsData) (b hsData)) (nthW F.R k) ∈ Subgroup.closure
      ((Subgroup.centralizer {wE (fF (a hsData) (b hsData)) F.Y1} : Set ↥(J hsData)) ∪
        Subgroup.centralizer {wE (fF (a hsData) (b hsData)) F.Y2}) :=
    hM.mem_of_stages (hM.mem_of_cl_letters hH ht hL) hMc hs hS
  refine hM.cover_of_cl Nat.prime_three (by rw [hcard, factorization_three]) hc hH ht hne ?_
  rw [eq_top_iff, ← closure_ab hsData, Subgroup.closure_le]
  have e0 : nthW F.R 0 = [0] := rfl
  have e1 : nthW F.R 1 = [2] := rfl
  have h0 := hR 0
  have h1 := hR 1
  rw [e0, wE_cons, wE_nil, one_mul, fF_zero] at h0
  rw [e1, wE_cons, wE_nil, one_mul, fF_two] at h1
  rintro x (rfl | rfl)
  · exact h0
  · exact h1

end CFSG.KD.SporCovF2.HS

end
