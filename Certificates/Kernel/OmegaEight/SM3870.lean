module

public import Certificates.Kernel.OmegaEight.SM3870K
public import CFSG.Certificates.Kernel.O8MatSound
public import CFSG.Certificates.Kernel.LocalCompAglSound
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSData
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SM3870

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KC.O8.Mat CFSG.KS CFSG.EvenSmallLie.OmegaEight
  CFSG.EvenSmallLie.OmegaEight.SpBranch
open CFSG.KLC.E8 (strictB_eq')

theorem matMulM_assoc (A B C : ℕ) : matMulM (matMulM A B) C = matMulM A (matMulM B C) :=
  eq_of_cols (matMulM_lt _ _) (matMulM_lt _ _) fun c hc => by
    rw [matMulM_col _ _ hc, matMulM_col _ _ hc, matMulM_col _ _ hc, matApp_matMulM]

theorem idCode_col : ∀ c < 8, idCode / 256 ^ c % 256 = 2 ^ c := by decide +kernel

theorem matMulM_id_left {A : ℕ} (hA : A < 2 ^ 64) : matMulM idCode A = A :=
  eq_of_cols (matMulM_lt _ _) hA fun c hc => by
    rw [matMulM_col _ _ hc, matApp_idCode _ (Nat.mod_lt _ (by norm_num))]

theorem matMulM_id_right {A : ℕ} (hA : A < 2 ^ 64) : matMulM A idCode = A :=
  eq_of_cols (matMulM_lt _ _) hA fun c hc => by
    rw [matMulM_col _ _ hc, idCode_col c hc, matApp_pow A hc]

theorem fld_eq (r o w : Nat) : Nat.land (Nat.shiftRight r o) (2 ^ w - 1) = r / 2 ^ o % 2 ^ w := by
  change (r >>> o) &&& (2 ^ w - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem actK_eq (i e : ℕ) : actK i e = sActRow i / 2 ^ (7 * e) % 2 ^ 7 :=
  fld_eq _ _ 7

theorem mtK_eq (i j : ℕ) : mtK i j = sMtRow i / 2 ^ (9 * j) % 2 ^ 9 := fld_eq _ _ 9

theorem ginvK_eq (i : ℕ) : ginvK i = sGinvLit / 2 ^ (9 * i) % 2 ^ 9 := fld_eq _ _ 9

theorem dK_eq (i : ℕ) : dK i = dLit / 2 ^ (64 * i) % 2 ^ 64 := fld_eq _ _ 64

theorem ix9_eq (T i : ℕ) : ix9 T i = T / 2 ^ (9 * i) % 2 ^ 9 := fld_eq _ _ 9

theorem kI' : Nat.beq (dK 0) CFSG.KC.O8.idK = true ∧ allN 512 dInvAt = true := (bAnd_iff _ _).1 kI

theorem sA_eq {i e : ℕ} (hi : i < 512) (he : e < 128) : sA i e = actK i e := by
  have hk : i * 128 + e < 65536 := by omega
  have e1 : (i * 128 + e) / 128 = i := by omega
  have e2 : (i * 128 + e) % 128 = e := by omega
  rw [sA, sAct, getElem!_pos _ _ (by simpa using hk), Array.getElem_ofFn, actK_eq]
  rw [e1, e2]

theorem sM_eq {i j : ℕ} (hi : i < 512) (hj : j < 512) : sM i j = mtK i j := by
  have hk : i * 512 + j < 262144 := by omega
  have e1 : (i * 512 + j) / 512 = i := by omega
  have e2 : (i * 512 + j) % 512 = j := by omega
  rw [sM, sMt, getElem!_pos _ _ (by simpa using hk), Array.getElem_ofFn, mtK_eq]
  rw [e1, e2]

theorem sGinv_eq {i : ℕ} (hi : i < 512) : sGinv[i]! = ginvK i := by
  rw [sGinv, getElem!_pos _ _ (by simpa using hi), Array.getElem_ofFn, ginvK_eq]

theorem mtK_lt (i j : ℕ) : mtK i j < 512 := by
  rw [mtK_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem ginvK_lt (i : ℕ) : ginvK i < 512 := by
  rw [ginvK_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem actK_lt (i e : ℕ) : actK i e < 128 := by
  rw [actK_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem dK_lt (i : ℕ) : dK i < 2 ^ 64 := by
  rw [dK_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem idK_eq' : CFSG.KC.O8.idK = idCode := by decide +kernel

theorem forall_of_blocks {f : Nat → Bool} {B k : Nat} (h : ∀ s < k, allBlk (B * s) f B = true) :
    ∀ i < B * k, f i = true := by
  intro i hi
  have hB : 0 < B := Nat.pos_of_ne_zero fun e => by simp [e] at hi
  have := allBlk_spec (h (i / B) (Nat.div_lt_of_lt_mul hi)) (i % B) (Nat.mod_lt i hB)
  rwa [Nat.add_eq, Nat.div_add_mod] at this

theorem hA {i e : ℕ} (hi : i < 512) (he : e < 128) : matApp (dK i) e = sA i e := by
  have h := allN_spec kA (128 * i + e) (by omega)
  unfold dAppAt at h
  have e1 : Nat.shiftRight (128 * i + e) 7 = i := by
    change (128 * i + e) >>> 7 = i
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have e2 : Nat.land (128 * i + e) 127 = e := by
    change (128 * i + e) &&& (2 ^ 7 - 1) = e
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [e1, e2, matAppK_eq] at h
  rw [sA_eq hi he]
  exact Nat.eq_of_beq_eq_true h

theorem hM {i j : ℕ} (hi : i < 512) (hj : j < 512) : matMulM (dK i) (dK j) = dK (sM i j) := by
  have hb : ∀ s < 16, allBlk (16384 * s) dMulAt 16384 = true := fun s hs => by
    interval_cases s
    exacts [kM0, kM1, kM2, kM3, kM4, kM5, kM6, kM7, kM8, kM9, kM10, kM11, kM12, kM13, kM14, kM15]
  have h := forall_of_blocks hb (512 * i + j) (by omega)
  unfold dMulAt at h
  simp only [strictB_eq'] at h
  have e1 : Nat.shiftRight (512 * i + j) 9 = i := by
    change (512 * i + j) >>> 9 = i
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have e2 : Nat.land (512 * i + j) 511 = j := by
    change (512 * i + j) &&& (2 ^ 9 - 1) = j
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [e1, e2, matMulK_eq] at h
  rw [sM_eq hi hj]
  exact Nat.eq_of_beq_eq_true h

theorem hI0 : dK 0 = idCode := by
  have h := kI'.1
  rw [← idK_eq']
  exact Nat.eq_of_beq_eq_true h

theorem hIinv {i : ℕ} (hi : i < 512) : matMulM (dK (sGinv[i]!)) (dK i) = idCode := by
  have h := allN_spec kI'.2 i hi
  unfold dInvAt at h
  rw [matMulK_eq] at h
  rw [sGinv_eq hi, ← idK_eq']
  exact Nat.eq_of_beq_eq_true h

theorem ix9_lt (T i : ℕ) : ix9 T i < 512 := by
  rw [ix9_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem sorted_mono {f : Nat → Nat} (h : ∀ a < 511, f a < f (a + 1)) :
    ∀ b < 512, ∀ a < b, f a < f b := by
  intro b
  induction b with
  | zero => intro _ a ha; omega
  | succ b ih =>
    intro hb a ha
    rcases Nat.lt_or_ge a b with h1 | h1
    · exact (ih (by omega) a h1).trans (h b (by omega))
    · have : a = b := by omega
      subst this
      exact h a (by omega)

theorem dK_inj {i j : ℕ} (hi : i < 512) (hj : j < 512) (e : dK i = dK j) : i = j := by
  have hs : ∀ a < 512, ix9 dSP (ix9 dSPI a) = a ∧
      (a < 511 → dK (ix9 dSP a) < dK (ix9 dSP (a + 1))) := by
    intro a ha
    have h := allN_spec kSort a ha
    unfold dSortAt at h
    simp only [bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h
    refine ⟨h.2.1, fun h' => ?_⟩
    have h3 := h.2.2
    have hb : Nat.blt a 511 = true := Nat.blt_eq.mpr h'
    rw [hb] at h3
    exact Nat.blt_eq.mp h3
  have hm := sorted_mono (f := fun a => dK (ix9 dSP a)) fun a ha => (hs a (by omega)).2 ha
  have hi2 := (hs i hi).1
  have hj2 := (hs j hj).1
  rw [← hi2, ← hj2] at e
  rcases Nat.lt_trichotomy (ix9 dSPI i) (ix9 dSPI j) with h | h | h
  · exact absurd e (Nat.ne_of_lt (hm _ (ix9_lt _ _) _ h))
  · rw [← hi2, ← hj2, h]
  · exact absurd e (Nat.ne_of_gt (hm _ (ix9_lt _ _) _ h))

theorem sM_lt' {i j : ℕ} (hi : i < 512) (hj : j < 512) : sM i j < 512 := by
  rw [sM_eq hi hj]
  exact mtK_lt _ _

theorem sA_lt' {i e : ℕ} (hi : i < 512) (he : e < 128) : sA i e < 128 := by
  rw [sA_eq hi he]
  exact actK_lt _ _

theorem sGinv_lt' {i : ℕ} (hi : i < 512) : sGinv[i]! < 512 := by
  rw [sGinv_eq hi]
  exact ginvK_lt _

theorem cert3870 : (sRangeCheck = true) ∧ (sAssocCheck = true) ∧ (sUnitCheck = true) ∧
    (sActCheck = true) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold sRangeCheck
    simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, List.all_eq_true, List.mem_range,
      decide_eq_true_eq]
    refine ⟨⟨⟨⟨by simp [sAct], by simp [sMt]⟩, fun k hk => ?_⟩, fun k hk => ?_⟩, fun i hi =>
      sGinv_lt' hi⟩
    · simp only [sAct, Array.size_ofFn] at hk
      simp only [sAct, Array.getElem_ofFn]
      exact Nat.mod_lt _ (by norm_num)
    · simp only [sMt, Array.size_ofFn] at hk
      simp only [sMt, Array.getElem_ofFn]
      exact Nat.mod_lt _ (by norm_num)
  · unfold sAssocCheck
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
    intro i hi j hj k hk
    refine dK_inj (sM_lt' (sM_lt' hi hj) hk) (sM_lt' hi (sM_lt' hj hk)) ?_
    rw [← hM (sM_lt' hi hj) hk, ← hM hi hj, ← hM hi (sM_lt' hj hk), ← hM hj hk, matMulM_assoc]
  · unfold sUnitCheck
    simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq]
    intro j hj
    refine ⟨⟨dK_inj (sM_lt' (by norm_num) hj) hj ?_, dK_inj (sM_lt' hj (by norm_num)) hj ?_⟩,
      dK_inj (sM_lt' (sGinv_lt' hj) hj) (by norm_num) ?_⟩
    · rw [← hM (by norm_num) hj, hI0, matMulM_id_left (dK_lt _)]
    · rw [← hM hj (by norm_num), hI0, matMulM_id_right (dK_lt _)]
    · rw [← hM (sGinv_lt' hj) hj, hIinv hj, hI0]
  · unfold sActCheck
    simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨fun g hg e he e' he' => ?_, fun g hg h hh e he => ?_⟩, fun e he => ?_⟩
    · have hx : e ^^^ e' < 128 := Nat.xor_lt_two_pow (n := 7) he he'
      rw [← hA hg hx, ← hA hg he, ← hA hg he', matApp_xor]
    · rw [← hA (sM_lt' hg hh) he, ← hM hg hh, matApp_matMulM, hA hh he, hA hg (sA_lt' hh he)]
    · rw [← hA (by norm_num) he, hI0, matApp_idCode _ (by omega)]

end CertificateChecks.KernelO8.SM3870

end
