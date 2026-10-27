module

public import Certificates.Kernel.ONSeven.B8134

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONS

open CFSG.KC.Enum CFSG.KS CFSG.KS.TW CFSG.KS.CB CFSG.ONSchreier CFSG.ONSchreier.Native
  CFSG.Sporadic.ON.Native CFSG.RankThree.Native
open CertificateChecks.KernelSpor.ON (TT UU stepF invF PARf LABf Mf small' rec_get parlab parlab2
  st1 st2 allBelowN_iff')
open CertificateChecks.KernelSpor.ON3 (LetM letM_invW)

theorem bad_get {r i : Nat} (hr : r < 5) (hi : i < (onSevenBadData[r]!).size) :
    (onSevenBadData[r]!)[i]! = (bd r).getD i (0, []) := by
  rw [← bd_get hr, getElem!_pos _ i hi, List.getD_eq_getElem _ _ (by simpa using hi)]
  rfl

theorem bad_size {r : Nat} (hr : r < 5) : (onSevenBadData[r]!).size = (bd r).length := by
  rw [← bd_get hr, Array.length_toList]

theorem bound_of {r : Nat} (hr : r < 5) {good : Nat} {useScan : Bool}
    (hX0 : WW (cw r) 0 = 0) (hcount : onSevenCount (onSevenConjArr r) = 49)
    (hgood : (onSevenGood (onSevenConjArr r)
      ((onSevenBadData[r]!).toList.map Prod.fst)).length = good)
    (hbad : ∀ i < (bd r).length, WW (uw r i) 0 = ((bd r).getD i (0, [])).1 ∧
      (if useScan then onSevenCosetFree (onSevenArr (uw r i)) (onSevenConjArr r)
        else onSevenCount (onSevenConjInv (onSevenArr (uw r i)) (onSevenConjArr r)) != 49) =
        true) :
    onSevenBoundCheck r (onSevenConjArr r) 49 good useScan = true := by
  unfold onSevenBoundCheck
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨?_, ?_⟩, hcount⟩, hgood⟩, allBelowN_iff'.2 fun i hi => ?_⟩
  · rw [tw_eq hr]
    exact pisInv_word (let_tw hr)
  · rw [xp_get hr (by norm_num), hX0]
  · have hi' : i < (bd r).length := bad_size hr ▸ hi
    obtain ⟨h0, h1⟩ := hbad i hi'
    rw [bad_get hr hi]
    have e : ((bd r).getD i (0, [])).2 = uw r i := rfl
    rw [e]
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨?_, pisInv_word (let_uw hr hi')⟩, h1⟩
    rw [arr_get (let_uw hr hi') (by norm_num), h0]

theorem small_facts {r : Nat} (hr : r < 5) : WW (cw r) 0 = 0 ∧
    (∀ k < 36, (AL r).getD k 0 = trK (stepF 2) (PARf 2) (LABf 2) 36 k (WW (cw r) 227759)) ∧
    ∀ i < (bd r).length, WW (uw r i) 0 = ((bd r).getD i (0, [])).1 ∧ (r < 3 →
      WW (bw r i) 0 = 0 ∧
      ∀ k < 36, (ABL r i).getD k 0 = trK (stepF 2) (PARf 2) (LABf 2) 36 k (WW (bw r i) 227759)) := by
  have h := List.all_eq_true.1 small_ok r (List.mem_range.2 hr)
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true',
    Nat.blt_eq] at h
  obtain ⟨⟨h0, hA⟩, hb⟩ := h
  refine ⟨h0, fun k hk => Nat.eq_of_beq_eq_true (allN_spec hA k hk), fun i hi => ?_⟩
  have h' := List.all_eq_true.1 hb i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true',
    Nat.blt_eq] at h'
  obtain ⟨hu, hrest⟩ := h'
  refine ⟨hu, fun h3 => ?_⟩
  rcases hrest with ⟨⟨-, hy⟩, hA'⟩ | hn
  · exact ⟨hy, fun k hk => Nat.eq_of_beq_eq_true (allN_spec hA' k hk)⟩
  · have hb3 : Nat.blt r 3 = true := by rw [Nat.blt_eq]; exact h3
    simp_all

theorem yp_get {r i : Nat} (hr : r < 5) (hi : i < (bd r).length) {j : Nat} (hj : j < 245520) :
    (onSevenConjInv (onSevenArr (uw r i)) (onSevenConjArr r))[j]! = WW (bw r i) j := by
  have hu := let_uw hr hi
  unfold onSevenConjInv
  rw [pcomp_get hj, arr_get hu hj, pcomp_get (WW_lt hj), xp_get hr (WW_lt hj),
    inv_get hu (WW_lt (WW_lt hj))]
  unfold bw
  rw [WW_append, WW_append, invL_eq]

theorem count_xp {r : Nat} (hr : r < 5) (hs : ∀ s < 26, ccR r s = true) :
    onSevenCount (onSevenConjArr r) = ∑ s ∈ Finset.range 26, (CL r).getD s 0 := by
  obtain ⟨h0, hA, -⟩ := small_facts hr
  exact count_slices (fun p hp => xp_get hr hp) h0 hA (fun p hp => WW_lt hp) hs

theorem count_bad {r i : Nat} (hr : r < 3) (hi : i < (bd r).length) {a b : Nat} (hab : a ≠ b)
    (ha : a < 26) (hb : b < 26) (h1 : cbR r i a = true) (h2 : cbR r i b = true)
    (h50 : 50 ≤ (CBL r i).getD a 0 + (CBL r i).getD b 0) :
    (onSevenCount (onSevenConjInv (onSevenArr (uw r i)) (onSevenConjArr r)) != 49) = true := by
  obtain ⟨-, -, hbd⟩ := small_facts (by omega : r < 5)
  obtain ⟨hy0, hyA⟩ := (hbd i hi).2 hr
  have hge := count_ge (fun p hp => yp_get (by omega) hi hp) hy0 hyA (fun p hp => WW_lt hp) hab ha hb
    h1 h2
  rw [bne_iff_ne, ne_eq]
  omega

theorem cfree {r : Nat} (hr : r < 5) (hb1 : (bd r).length = 1)
    (hs : ∀ s < 26, cfR r s = true) :
    onSevenCosetFree (onSevenArr (uw r 0)) (onSevenConjArr r) = true := by
  obtain ⟨-, hA, -⟩ := small_facts hr
  have hu := let_uw hr (by omega : 0 < (bd r).length)
  obtain ⟨-, -, -, m1, m2, hf₁, hf₂⟩ := small'
  unfold onSevenCosetFree onSevenCosetFreeAt
  refine allBelowN_iff'.2 fun k₁ hk₁ => allBelowN_iff'.2 fun k₂ hk₂ => ?_
  have hk₁' : k₁ < Mf 1 := by rw [m1]; exact hk₁
  have hk₂' : k₂ < Mf 2 := by rw [m2]; exact hk₂
  have hsk := hs (k₁ / 2048) (by omega)
  unfold cfR cfS at hsk
  have hsl := allN_spec hsk (k₁ % 2048) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 2048 (k₁ / 2048)) (k₁ % 2048) = k₁ := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  beta_reduce at hsl
  have hbk : Nat.blt k₁ 52136 = true := by rw [Nat.blt_eq]; exact hk₁
  rw [e, CFSG.KS.CB.strictB_app', hbk] at hsl
  have hc : cfK (WW (uw r 0)) (WW (invL (uw r 0))) (WW (cw r)) (fun k => (AL r).getD k 0)
      (stepF 1) (invF 1) (PARf 1) (LABf 1) (Mf 1) (stepF 2) (PARf 2) (LABf 2) (Mf 2) 227759 100817
      k₁ = true := by
    rw [m1, m2]
    exact hsl
  have ht := cosetTest_false (levels := onSevenLevels) (stepsAll := onSevenSteps) (i₁ := 1)
    (i₂ := 2) (b₀ := 0) (rec_get (by norm_num)) (rec_get (by norm_num)) (parlab (by norm_num))
    parlab2 st1 st2 (fun j hj => (hf₂ j hj).2)
    (fun p hp => ⟨arr_get hu hp, WW_lt hp, WW_inv hu hp⟩) (fun p hp => ⟨xp_get hr hp, WW_lt hp⟩)
    (by norm_num) (fun k hk => by rw [m2] at hk ⊢; exact hA k hk) hk₁' hc hk₂'
  unfold onSevenCosetTestAt onSevenBase
  rw [ht]
  rfl

theorem bound_count {r : Nat} (hr : r < 3) {good : Nat} (hcc : ∀ s < 26, ccR r s = true)
    (hsum : ∑ s ∈ Finset.range 26, (CL r).getD s 0 = 49) (hfx : ∀ s < 8, fxR r s = true)
    (hg : ∑ s ∈ Finset.range 8, (FL r).getD s 0 = good) (hb2 : (bd r).length = 2)
    (hbad : ∀ i < 2, ∃ a b, a ≠ b ∧ a < 26 ∧ b < 26 ∧ cbR r i a = true ∧ cbR r i b = true ∧
      50 ≤ (CBL r i).getD a 0 + (CBL r i).getD b 0) :
    onSevenBoundCheck r (onSevenConjArr r) 49 good false = true := by
  have hr5 : r < 5 := by omega
  obtain ⟨h0, -, hbd⟩ := small_facts hr5
  refine bound_of hr5 h0 ((count_xp hr5 hcc).trans hsum) ((good_slices hr5 hfx).trans hg)
    fun i hi => ⟨(hbd i hi).1, ?_⟩
  obtain ⟨a, b, hab, ha, hb, h1, h2, h50⟩ := hbad i (by omega)
  exact count_bad hr hi hab ha hb h1 h2 h50

theorem bound_scan {r : Nat} (hr : r < 5) {good : Nat} (hcc : ∀ s < 26, ccR r s = true)
    (hsum : ∑ s ∈ Finset.range 26, (CL r).getD s 0 = 49) (hfx : ∀ s < 8, fxR r s = true)
    (hg : ∑ s ∈ Finset.range 8, (FL r).getD s 0 = good) (hb1 : (bd r).length = 1)
    (hcf : ∀ s < 26, cfR r s = true) :
    onSevenBoundCheck r (onSevenConjArr r) 49 good true = true := by
  obtain ⟨h0, -, hbd⟩ := small_facts hr
  refine bound_of hr h0 ((count_xp hr hcc).trans hsum) ((good_slices hr hfx).trans hg)
    fun i hi => ⟨(hbd i hi).1, ?_⟩
  have : i = 0 := by omega
  subst this
  exact cfree hr hb1 hcf

theorem facts8134 : onSevenBoundCheck 0 (onSevenConjArr 0) 49 28 false = true ∧
    onSevenBoundCheck 1 (onSevenConjArr 1) 49 28 false = true ∧
    onSevenBoundCheck 2 (onSevenConjArr 2) 49 28 false = true ∧
    onSevenBoundCheck 3 (onSevenConjArr 3) 49 1 true = true ∧
    onSevenBoundCheck 4 (onSevenConjArr 4) 49 1 true = true := by
  refine ⟨bound_count (r := 0) (by norm_num) cc0All (by decide +kernel) fx0All (by decide +kernel)
      (by decide) fun i hi => ?_,
    bound_count (r := 1) (by norm_num) cc1All (by decide +kernel) fx1All (by decide +kernel)
      (by decide) fun i hi => ?_,
    bound_count (r := 2) (by norm_num) cc2All (by decide +kernel) fx2All (by decide +kernel)
      (by decide) fun i hi => ?_,
    bound_scan (r := 3) (by norm_num) cc3All (by decide +kernel) fx3All (by decide +kernel)
      (by decide) cf3All,
    bound_scan (r := 4) (by norm_num) cc4All (by decide +kernel) fx4All (by decide +kernel)
      (by decide) cf4All⟩
  · interval_cases i
    · exact ⟨0, 3, by decide, by decide, by decide, cb00S0, cb00S3, by decide +kernel⟩
    · exact ⟨0, 1, by decide, by decide, by decide, cb01S0, cb01S1, by decide +kernel⟩
  · interval_cases i
    · exact ⟨0, 3, by decide, by decide, by decide, cb10S0, cb10S3, by decide +kernel⟩
    · exact ⟨0, 1, by decide, by decide, by decide, cb11S0, cb11S1, by decide +kernel⟩
  · interval_cases i
    · exact ⟨0, 1, by decide, by decide, by decide, cb20S0, cb20S1, by decide +kernel⟩
    · exact ⟨0, 3, by decide, by decide, by decide, cb21S0, cb21S3, by decide +kernel⟩

end CertificateChecks.KernelSpor.ONS

end
