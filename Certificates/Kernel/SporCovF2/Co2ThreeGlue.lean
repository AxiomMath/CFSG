module

public import Certificates.Kernel.SporCovF2.Co2Three
public import Certificates.Kernel.SporCovF2.Co2FiveGlue
public import CFSG.Certificates.Kernel.SporCov.F2Reg
public import CFSG.Certificates.Kernel.SporCov.CensusSound

public section

namespace CFSG.KD.SporCovF2.Co2Three

open CFSG.KC.SporCov CFSG.KD.SporCov CFSG.StandardType.SporadicShape CFSG.Sporadic.SmallF2
open CFSG.Sporadic.Co2.Native (co2Data)

theorem factorization_three : (42305421312000 : ℕ).factorization 3 = 6 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.factorization_def _ Nat.prime_three]
  have e : (42305421312000 : ℕ) = 3 ^ 6 * 58032128000 := by norm_num
  rw [e, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 58032128000), add_zero]

theorem generating_of_clC {E : List ℕ → List ℕ → Bool} {f : ℕ → ↥(J co2Data)}
    (hM : Model L E (wE f)) (hf : ∀ c < 4, f c = fF (a co2Data) (b co2Data) c)
    {t y₁ y₂ g₁ g₂ : List ℕ} {M C : List (List ℕ)} {n nL : ℕ}
    (h : clC E t y₁ y₂ g₁ g₂ M n nL C = true) :
    ∀ y, IsConj (wE f t) y → SporKRestGenerating 3 y := by
  unfold clC at h
  simp only [Bool.and_eq_true, allLt_iff] at h
  obtain ⟨⟨⟨⟨hH, hL⟩, hs⟩, hS⟩, ht⟩ := h
  refine hM.generating_of_cl Nat.prime_three hH ht ?_
  have hMc : chA L M = true := (hM.clH_facts hH ht).2.1
  have hR := hM.mem_of_stages (hM.mem_of_cl_letters hH ht hL) hMc hs hS
  rw [eq_top_iff, ← closure_ab co2Data, Subgroup.closure_le]
  have h0 := hR 0
  have h1 := hR 1
  have e0 : nthW F.Rs 0 = [0] := rfl
  have e1 : nthW F.Rs 1 = [2] := rfl
  rw [e0, wE_cons, wE_nil, one_mul, hf 0 (by norm_num), fF_zero] at h0
  rw [e1, wE_cons, wE_nil, one_mul, hf 2 (by norm_num), fF_two] at h1
  rintro x (rfl | rfl)
  · exact h0
  · exact h1

theorem sporKRestCover_three_J :
    SporKRestCover 3 ↥(J co2Data) := by
  obtain ⟨E, K, f, hk, hM, hc, hK, hf⟩ := kitR_J (co2Data ()) CertificateChecks.KernelVec.Co2.hA
    CertificateChecks.KernelVec.Co2.hB Co2Five.Ck.bA Co2Five.Ck.bB Ck.ok
  unfold chk at hk
  simp only [Bool.and_eq_true, allLt_iff] at hk
  obtain ⟨⟨⟨⟨⟨hR, hH⟩, hI⟩, hT⟩, h0⟩, h1⟩ := hk
  have hRp : F.Rp = [nthW F.Rp 0, nthW F.Rp 1] := rfl
  refine hM.cover_of_cen (k := 6) (H := F.H) (R := F.R) (Rp := F.Rp) (Gs := F.Gs) (T := F.T)
    (P := F.P) Nat.prime_three
    (by rw [Co2Five.card_J, factorization_three]) hc K hK
    (fun i hi j hj hij => ?_) hH hI hT ?_
  · have e := hR i hi j hj
    rwa [(by rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; omega : Nat.blt j i = false),
      Bool.false_or] at e
  · rw [hRp]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact generating_of_clC hM hf h0
    · exact generating_of_clC hM hf h1

end CFSG.KD.SporCovF2.Co2Three

end
