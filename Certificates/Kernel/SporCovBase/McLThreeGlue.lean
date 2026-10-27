module

public import Certificates.Kernel.SporCovBase.McLThree
public import Certificates.Kernel.Sporadic.McLK.Final
public import CFSG.Certificates.Kernel.SporCov.BaseReg
public import CFSG.Certificates.Kernel.SporCov.PClM
public import CFSG.Certificates.Kernel.SporCov.CenL
public import CFSG.Sporadic.McL.Simple

public section

namespace CFSG.KD.SporCovBase.McLThree

open CFSG.KC.SporCov CFSG.KD.SporCov CFSG.StandardType.SporadicShape CFSG.Sporadic.Th
  CFSG.KS.PEnum CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow
open CFSG.Sporadic.McL (J a b)
open CertificateChecks.KernelSpor.McLK (AL BE BI)


theorem hA : ∀ x < 275, r32 AL x = idx 275 a x := fun x hx => by
  have h := CFSG.Sporadic.McL.rep_alpha x hx
  unfold CFSG.Sporadic.McL.orb at h
  rwa [CertificateChecks.KernelSpor.McLK.orb_eq.1, CertificateChecks.KernelSpor.McLK.al_get hx] at h

theorem hB : ∀ x < 275, r32 BE x = idx 275 b x := fun x hx => by
  have h := CFSG.Sporadic.McL.rep_beta x hx
  unfold CFSG.Sporadic.McL.orb at h
  rwa [CertificateChecks.KernelSpor.McLK.orb_eq.1, CertificateChecks.KernelSpor.McLK.be_get hx] at h

theorem hAi : ∀ x < 275, r32 AL x = idx 275 a⁻¹ x :=
  inv_of_left hA fun _ hx => (CertificateChecks.KernelSpor.McLK.inv_facts hx).2.1

theorem hBi : ∀ x < 275, r32 BI x = idx 275 b⁻¹ x :=
  inv_of_left hB fun _ hx => (CertificateChecks.KernelSpor.McLK.inv_facts hx).2.2.2.1

theorem nthN_mem : ∀ {l : List ℕ} {i : ℕ}, i < l.length → nthN l i ∈ l
  | [], _, h => absurd h (by simp)
  | x :: l, 0, _ => List.mem_cons_self
  | x :: l, i + 1, h => by
    rw [nthN_cons_succ]
    exact List.mem_cons_of_mem _ (nthN_mem (by simp at h; omega))

theorem sep_bs (g : J) (h : ∀ j ∈ F.bs, idx 275 g (lg j) = lg j) : g = 1 := by
  have hb := Ck.base
  rw [Bool.and_eq_true, allLt_iff] at hb
  obtain ⟨hl, hb⟩ := hb
  have hlen : F.bs.length = 21 := by rw [← lenN_eq]; exact Nat.eq_of_beq_eq_true hl
  apply CFSG.Sporadic.McL.sep g
  intro t ht
  have hs : CFSG.Sporadic.McL.Native.chainQ.size = 21 := rfl
  rw [hs] at ht
  have hQ : CFSG.Sporadic.McL.Native.chainQ[t]! = nthN Q t := by
    interval_cases t <;> rfl
  have e := h _ (nthN_mem (by rw [hlen]; exact ht))
  rw [Nat.eq_of_beq_eq_true (hb t ht)] at e
  rw [hQ]
  exact e

theorem factorization_three : (898128000 : ℕ).factorization 3 = 6 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.factorization_def _ Nat.prime_three]
  have e : (898128000 : ℕ) = 3 ^ 6 * 1232000 := by norm_num
  rw [e, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 1232000), add_zero]

theorem sporKRestCover_three_J : SporKRestCover 3 ↥J := by
  obtain ⟨E, K, f, hk, hM, hc, hK, hf⟩ := kitB_sound hA hAi hB hBi sep_bs Ck.ok
  unfold chk at hk
  simp only [Bool.and_eq_true, allLt_iff] at hk
  obtain ⟨⟨⟨⟨⟨⟨hR, hH⟩, hI⟩, hT⟩, hrc⟩, h0⟩, h1⟩ := hk
  have hR' : ∀ i < 6, ∀ j < 6, i ≤ j → pcR E 3 F.H F.R 6 i j = true := fun i hi j hj hij => by
    have e := hR i hi j hj
    rwa [(by rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; omega : Nat.blt j i = false),
      Bool.false_or] at e
  have hH' := hH
  unfold cenH at hH'
  simp only [Bool.and_eq_true] at hH'
  obtain ⟨⟨⟨⟨oH, oRp⟩, -⟩, -⟩, hlen⟩ := hH'
  have hlen' : F.P.length = 3 ^ 6 := by
    have e := Nat.eq_of_beq_eq_true hlen
    rw [lenN_eq] at e
    rw [e]
    norm_num
  have hS₀ : IsPGroup 3 (Subgroup.closure {x : J | ∃ j < 6, x = wE f (nthW F.H j)}) := by
    rw [closure_eq_pcSub (fun j => wE f (nthW F.H j)) 6]
    exact IsPGroup.of_card (hM.pcSub_card_of_cen Nat.prime_three K hK oH hR' hlen' hI)
  have htop : ∀ T : Subgroup J, (∀ k, wE f (nthW Rs k) ∈ T) → T = ⊤ := by
    intro T hT
    rw [eq_top_iff, ← CFSG.Sporadic.McL.closure_ab, Subgroup.closure_le]
    have e0 : nthW Rs 0 = [0] := rfl
    have e1 : nthW Rs 1 = [2] := rfl
    have g0 := hT 0
    have g1 := hT 1
    rw [e0, wE_cons, wE_nil, one_mul, hf 0 (by norm_num), fP_zero] at g0
    rw [e1, wE_cons, wE_nil, one_mul, hf 2 (by norm_num), fP_two] at g1
    rintro x (rfl | rfl)
    · exact g0
    · exact g1
  have hcl : ∀ c < 2, chW L (tOf c) = true ∧
      ∀ y, IsConj (wE f (tOf c)) y → SporKRestGenerating 3 y := by
    intro c hc
    interval_cases c
    · exact hM.generating_of_pclMOK Nat.prime_three hS₀ oH h0 htop
    · exact hM.generating_of_pclMOK Nat.prime_three hS₀ oH h1 htop
  refine hM.cover_of_cen (k := 6) (H := F.H) (R := F.R) (Rp := F.Rp) (Gs := F.Gs) (T := F.T)
    (P := F.P) Nat.prime_three (by rw [CFSG.Sporadic.McL.card_J, factorization_three]) hc K hK
    hR' hH hI (fun n hn => cenOK_of_cenE (cenAll_spec hT n (by rw [hlen']; exact hn))) ?_
  intro r hr y hy
  obtain ⟨i, hi, rfl⟩ := exists_nthW F.Rp r hr
  unfold rcOK at hrc
  rw [allLt_iff, lenW_eq] at hrc
  have hri := hrc i hi
  rw [Bool.and_eq_true, Bool.and_eq_true] at hri
  obtain ⟨⟨hc2, og⟩, hcj⟩ := hri
  obtain ⟨ot, hgen⟩ := hcl _ (Nat.le_of_ble_eq_true hc2)
  have oR := (chA_iff _ _).1 oRp _ (nthW_mem hi)
  exact hgen y ((isConj_of_conj (hM.conj ot og oR hcj)).trans hy)

end CFSG.KD.SporCovBase.McLThree

end
