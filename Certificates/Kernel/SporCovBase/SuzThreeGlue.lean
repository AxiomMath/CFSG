module

public import Certificates.Kernel.SporCovBase.SuzThree
public import Certificates.Kernel.SporCovBase.SuzGlue
public import CFSG.Certificates.Kernel.SporCov.BaseReg
public import CFSG.Certificates.Kernel.SporCov.PClM
public import CFSG.Certificates.Kernel.SporCov.CenL

public section

namespace CFSG.KD.SporCovBase.SuzThree

open CFSG.KC.SporCov CFSG.KD.SporCov CFSG.StandardType.SporadicShape CFSG.Sporadic.Th
  CFSG.KS.PEnum CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow
open CFSG.Sporadic.Suz (J a b)
open CertificateChecks.KernelSpor.SuzK (AL BE)


theorem hBi3 : ∀ x < 22880, fBi x = idx 22880 b⁻¹ x := fun x hx => Suz.hBi x hx

theorem nthN_mem : ∀ {l : List ℕ} {i : ℕ}, i < l.length → nthN l i ∈ l
  | [], _, h => absurd h (by simp)
  | x :: l, 0, _ => List.mem_cons_self
  | x :: l, i + 1, h => by
    rw [nthN_cons_succ]
    exact List.mem_cons_of_mem _ (nthN_mem (by simp at h; omega))

theorem sep_bs3 (g : J) (h : ∀ j ∈ F.bs, idx 22880 g (lg j) = lg j) : g = 1 := by
  have hb := Ck.base
  rw [Bool.and_eq_true, allLt_iff] at hb
  obtain ⟨hl, hb⟩ := hb
  have hlen : F.bs.length = 6 := by rw [← lenN_eq]; exact Nat.eq_of_beq_eq_true hl
  set γ := wE (fP a b) F.gw
  have himg : ∀ t < 6, lg (nthN F.bs t) = idx 22880 γ t := fun t ht => by
    rw [← Nat.eq_of_beq_eq_true (hb t ht), imB_eq Suz.hA Suz.hAi Suz.hB hBi3 F.gw (by omega)]
  have e : γ⁻¹ * g * γ = 1 := Suz.sep_bs _ fun x hx => by
    have hx6 : x < 6 := by
      simp only [Suz.bs, List.mem_cons, List.not_mem_nil, or_false] at hx
      omega
    have := h _ (nthN_mem (by rw [hlen]; exact hx6))
    rw [himg x hx6] at this
    rw [idx_mul, idx_mul, this, idx_inv_idx]
  have e2 : g = γ * (γ⁻¹ * g * γ) * γ⁻¹ := by group
  rw [e2, e, mul_one, mul_inv_cancel]

theorem factorization_three : (448345497600 : ℕ).factorization 3 = 7 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.factorization_def _ Nat.prime_three]
  have e : (448345497600 : ℕ) = 3 ^ 7 * 205004800 := by norm_num
  rw [e, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 205004800), add_zero]

theorem sporKRestCover_three_J : SporKRestCover 3 ↥J := by
  obtain ⟨E, K, f, hk, hM, hc, hK, hf⟩ :=
    kitB_sound Suz.hA Suz.hAi Suz.hB hBi3 sep_bs3 Ck.ok
  unfold chk at hk
  simp only [Bool.and_eq_true, allLt_iff] at hk
  obtain ⟨⟨⟨⟨⟨⟨⟨hR, hH⟩, hI⟩, hT⟩, hrc⟩, h0⟩, h1⟩, h2⟩ := hk
  have hR' : ∀ i < 7, ∀ j < 7, i ≤ j → pcR E 3 F.H F.R 7 i j = true := fun i hi j hj hij => by
    have e := hR i hi j hj
    rwa [(by rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; omega : Nat.blt j i = false),
      Bool.false_or] at e
  have hH' := hH
  unfold cenH at hH'
  simp only [Bool.and_eq_true] at hH'
  obtain ⟨⟨⟨⟨oH, oRp⟩, -⟩, -⟩, hlen⟩ := hH'
  have hlen' : F.P.length = 3 ^ 7 := by
    have e := Nat.eq_of_beq_eq_true hlen
    rw [lenN_eq] at e
    rw [e]
    norm_num
  have hS₀ : IsPGroup 3 (Subgroup.closure {x : J | ∃ j < 7, x = wE f (nthW F.H j)}) := by
    rw [closure_eq_pcSub (fun j => wE f (nthW F.H j)) 7]
    exact IsPGroup.of_card (hM.pcSub_card_of_cen Nat.prime_three K hK oH hR' hlen' hI)
  have htop : ∀ T : Subgroup J, (∀ k, wE f (nthW Rs k) ∈ T) → T = ⊤ := by
    intro T hT
    rw [eq_top_iff, ← CFSG.Sporadic.Suz.closure_ab, Subgroup.closure_le]
    have e0 : nthW Rs 0 = [0] := rfl
    have e1 : nthW Rs 1 = [2] := rfl
    have g0 := hT 0
    have g1 := hT 1
    rw [e0, wE_cons, wE_nil, one_mul, hf 0 (by norm_num), fP_zero] at g0
    rw [e1, wE_cons, wE_nil, one_mul, hf 2 (by norm_num), fP_two] at g1
    rintro x (rfl | rfl)
    · exact g0
    · exact g1
  have hcl : ∀ c < 3, chW L (tOf c) = true ∧
      ∀ y, IsConj (wE f (tOf c)) y → SporKRestGenerating 3 y := by
    intro c hc
    interval_cases c
    · exact hM.generating_of_pclMOK Nat.prime_three hS₀ oH h0 htop
    · exact hM.generating_of_pclMOK Nat.prime_three hS₀ oH h1 htop
    · exact hM.generating_of_pclMOK Nat.prime_three hS₀ oH h2 htop
  refine hM.cover_of_cen (k := 7) (H := F.H) (R := F.R) (Rp := F.Rp) (Gs := F.Gs) (T := F.T)
    (P := F.P) Nat.prime_three (by rw [CFSG.Sporadic.Suz.card_J, factorization_three]) hc K hK
    hR' hH hI (fun n hn => cenOK_of_cenE (cenAll_spec hT n (by rw [hlen']; exact hn))) ?_
  intro r hr y hy
  obtain ⟨i, hi, rfl⟩ := exists_nthW F.Rp r hr
  unfold rcOK at hrc
  rw [allLt_iff, lenW_eq] at hrc
  have hri := hrc i hi
  rw [Bool.and_eq_true, Bool.and_eq_true] at hri
  obtain ⟨⟨hc3, og⟩, hcj⟩ := hri
  obtain ⟨ot, hgen⟩ := hcl _ (Nat.le_of_ble_eq_true hc3)
  have oR := (chA_iff _ _).1 oRp _ (nthW_mem hi)
  exact hgen y ((isConj_of_conj (hM.conj ot og oR hcj)).trans hy)

end CFSG.KD.SporCovBase.SuzThree

end
