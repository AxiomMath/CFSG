module

public import Certificates.Kernel.SporCovF2.Co3Three
public import CFSG.Certificates.Kernel.SporCov.F2Reg
public import CFSG.Certificates.Kernel.SporCov.PClM
public import CFSG.Certificates.Kernel.SporCov.CenL
public import CFSG.Sporadic.Bridge.Co3Surj
public import Certificates.Kernel.SporCovF2.Co3

public section

namespace CFSG.KD.SporCovF2.Co3Three

open CFSG.KC.SporCov CFSG.KD.SporCov CFSG.StandardType.SporadicShape CFSG.Sporadic.SmallF2
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow
open CFSG.Sporadic.Co3.Native (co3Data)

theorem factorization_three : (495766656000 : ℕ).factorization 3 = 7 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.factorization_def _ Nat.prime_three]
  have e : (495766656000 : ℕ) = 3 ^ 7 * 226688000 := by norm_num
  rw [e, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 226688000), add_zero]

theorem sporKRestCover_three_J :
    SporKRestCover 3 ↥(J co3Data) := by
  obtain ⟨E, K, f, hk, hM, hc, hK, hf⟩ := kitR_J (co3Data ()) CertificateChecks.KernelVec.Co3.hA
    CertificateChecks.KernelVec.Co3.hB Co3.Ck.bA Co3.Ck.bB Ck.ok
  unfold chk at hk
  simp only [Bool.and_eq_true, allLt_iff] at hk
  obtain ⟨⟨⟨⟨⟨⟨hR, hH⟩, hI⟩, hT⟩, h0⟩, h1⟩, h2⟩ := hk
  have hR' : ∀ i < 7, ∀ j < 7, i ≤ j → pcR E 3 F.H F.R 7 i j = true := fun i hi j hj hij => by
    have e := hR i hi j hj
    rwa [(by rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; omega : Nat.blt j i = false),
      Bool.false_or] at e
  have hH' := hH
  unfold cenH at hH'
  simp only [Bool.and_eq_true] at hH'
  obtain ⟨⟨⟨⟨oH, -⟩, -⟩, -⟩, hlen⟩ := hH'
  have hlen' : F.P.length = 3 ^ 7 := by
    have e := Nat.eq_of_beq_eq_true hlen
    rw [lenN_eq] at e
    rw [e]
    norm_num
  have hS₀ : IsPGroup 3 (Subgroup.closure {x : ↥(J co3Data) | ∃ j < 7, x = wE f (nthW F.H j)}) := by
    rw [closure_eq_pcSub (fun j => wE f (nthW F.H j)) 7]
    exact IsPGroup.of_card (hM.pcSub_card_of_cen Nat.prime_three K hK oH hR' hlen' hI)
  have htop : ∀ T : Subgroup ↥(J co3Data), (∀ k, wE f (nthW Rs k) ∈ T) → T = ⊤ := by
    intro T hT
    rw [eq_top_iff, ← closure_ab co3Data, Subgroup.closure_le]
    have e0 : nthW Rs 0 = [0] := rfl
    have e1 : nthW Rs 1 = [2] := rfl
    have g0 := hT 0
    have g1 := hT 1
    rw [e0, wE_cons, wE_nil, one_mul, hf 0 (by norm_num), fF_zero] at g0
    rw [e1, wE_cons, wE_nil, one_mul, hf 2 (by norm_num), fF_two] at g1
    rintro x (rfl | rfl)
    · exact g0
    · exact g1
  have hRp : F.Rp = [nthW F.Rp 0, nthW F.Rp 1, nthW F.Rp 2] := rfl
  refine hM.cover_of_cen (k := 7) (H := F.H) (R := F.R) (Rp := F.Rp) (Gs := F.Gs) (T := F.T)
    (P := F.P) Nat.prime_three (by rw [CFSG.Sporadic.Bridge.Co3.card_J, factorization_three]) hc K
    hK hR' hH hI (fun n hn => cenOK_of_cenE (cenAll_spec hT n (by rw [hlen']; exact hn))) ?_
  rw [hRp]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hM.generating_of_pclMOK Nat.prime_three hS₀ oH h0 htop).2
  · exact (hM.generating_of_pclMOK Nat.prime_three hS₀ oH h1 htop).2
  · exact (hM.generating_of_pclMOK Nat.prime_three hS₀ oH h2 htop).2

end CFSG.KD.SporCovF2.Co3Three

end
