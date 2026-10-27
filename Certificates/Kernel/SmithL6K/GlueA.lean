module

public import Certificates.Kernel.SmithL6K.GlueD
public import Certificates.Kernel.SmithL6K.GlueO
public import Certificates.Kernel.SmithL6K.ChecksA
public import CFSG.Certificates.Kernel.SmithL6KASound
public import Certificates.Data.SmithL6Facts

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K CFSG.SmithL6.Kernel
open CFSG.SmithE (applyCols)

theorem wtIdx_wt {j : Nat} (hj : j < 1395) : wtIdx[wt j]! = j := by
  unfold wtIdx
  exact foldl_set_last (f := fun j => wtArr[j]!) (wt_lt20K j) hj (wtArr_get hj)
    fun j' h1 h2 e => by
      rw [wtArr_get h2] at e
      have := wt_inj j' h2 j hj e
      omega

theorem isWt_iff (v : Nat) : mfIsWt v = true ↔ ∃ l < 1395, wt l = v := by
  unfold mfIsWt
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨_, h1, by rw [← wtArr_get h1]; exact h2⟩
  · rintro ⟨l, hl, rfl⟩
    rw [wtIdx_wt hl, wtArr_get hl]
    exact ⟨hl, rfl⟩

theorem adjM_iff {i j : Nat} (hi : i < 1395) (hj : j < 1395) :
    adjM i j = true ↔ 4 ≤ (setM (wMask i) ∩ setM (wMask j)).card := by
  unfold adjM
  rw [maskArr_get hi, maskArr_get hj, atLeast4_iff (inter_facts hi hj).1, setM_and]

theorem wtd_get {i : Nat} (hi : i < 1395) : wtd.getD i 0 = wt i := (wt_eq hi).symm

theorem wmk_get {i : Nat} (hi : i < 1395) : wmk.getD i 0 = wMask i := (wMask_eq hi).symm

theorem adj_all : ∀ i < 1395, ∃ j < 1395, j ≠ i ∧ 4 ≤ (setM (wMask i) ∩ setM (wMask j)).card := by
  refine reach_planes (fun i => ∃ j < 1395, j ≠ i ∧ 4 ≤ (setM (wMask i) ∩ setM (wMask j)).card)
    (fun v _ hv => ?_) ?_
  · rw [beq_iff_eq.mp hv]
    have h := adj_row0
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨j, hj, h4, hne⟩ := h
    rw [wmk_get (by decide), wmk_get hj] at h4
    rw [wtd_get hj, wtd_get (by decide)] at hne
    refine ⟨j, hj, fun e => hne (by rw [e]), ?_⟩
    rw [← setM_and]
    exact (atLeast4_iff (inter_facts (by decide) hj).1).mp h4
  · intro s hs u hu v _ he hQ
    rw [← beq_iff_eq.mp he]
    obtain ⟨j, hj, hne, h4⟩ := hQ
    refine ⟨_, (row_facts s hs j hj).1, fun e => hne ?_, by rw [img_meet hs hu hj]; exact h4⟩
    rw [← img_invol hs hj, e, img_invol hs hu]

theorem sum_all : ∀ i < 1395, ∀ j < 1395, 4 ≤ (setM (wMask i) ∩ setM (wMask j)).card ∨
    ∀ l < 1395, wt l ≠ wt i ^^^ wt j := by
  refine reach_planes (fun i => ∀ j < 1395, 4 ≤ (setM (wMask i) ∩ setM (wMask j)).card ∨
    ∀ l < 1395, wt l ≠ wt i ^^^ wt j) (fun v _ hv => ?_) ?_
  · rw [beq_iff_eq.mp hv]
    intro j hj
    have h := sumRowK_get sum_row0 j (by rw [wtd_length]; exact hj) (by rw [wmk_length]; exact hj)
    rw [wmk_get (by decide), wmk_get hj, wtd_get (by decide), wtd_get hj, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [← setM_and]
      exact Or.inl ((atLeast4_iff (inter_facts (by decide) hj).1).mp h)
    · refine Or.inr fun l hl e => ?_
      have hmem : wt l ∈ wtd := by
        rw [← wtd_get hl, getD_of_lt (by rw [wtd_length]; exact hl)]
        exact List.getElem_mem _
      have hb : (maskOf wtd).testBit (wt l) = true := by
        unfold maskOf
        rw [maskOf_testBit, Nat.zero_testBit, Bool.false_or]
        simpa using hmem
      rw [e] at hb
      simp [hb] at h
  · intro s hs u hu v _ he hQ
    rw [← beq_iff_eq.mp he]
    intro j hj
    have hg := gns_lt s hs
    have hj' := (row_facts s hs j hj).1
    have hjj := img_invol hs hj
    rcases hQ _ hj' with h | h
    · left
      rw [← hjj, img_meet hs hu hj']
      exact h
    · right
      intro l hl e
      obtain ⟨hl', hwl, -⟩ := row_facts s hs l hl
      have hwj := (row_facts s hs _ hj').2.1
      rw [hjj] at hwj
      refine h _ hl' ?_
      rw [hwl, e, applyCols_xorL, (row_facts s hs u hu).2.1, tvCols_invol hg _ (wt_lt20K u), hwj,
        tvCols_invol hg _ (wt_lt20K _)]

theorem mfChkWt_holds : mfChkWt = true := by
  have h0 := wtd_ne0
  rw [List.all_eq_true] at h0
  unfold mfChkWt
  simp only [List.all_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.or_eq_true, Bool.not_eq_true']
  refine ⟨fun j hj => by rw [wtArr_get hj, wtIdx_wt hj], fun i hi => ?_⟩
  rw [wtArr_get hi]
  refine ⟨⟨⟨wt_lt20K i, ?_⟩, ?_⟩, fun j hj => ?_⟩
  · have e := h0 (wt i) (by
      rw [← wtd_get hi, getD_of_lt (by rw [wtd_length]; exact hi)]
      exact List.getElem_mem _)
    simpa using e
  · obtain ⟨j, hj, hne, h4⟩ := adj_all i hi
    exact ⟨j, hj, (adjM_iff hi hj).mpr h4, by
      rw [wtArr_get hj]
      exact fun e => hne (wt_inj j hj i hi e)⟩
  · rw [wtArr_get hj, adjM_iff hi hj]
    rcases sum_all i hi j hj with h | h
    · exact Or.inl h
    · right
      cases e : mfIsWt (wt i ^^^ wt j)
      · rfl
      · obtain ⟨l, hl, el⟩ := (isWt_iff _).mp e
        exact absurd el (h l hl)

theorem clo_all : ∀ k < 1953, Clo k := by
  have hlen : 0 < gns.length := by rw [gns_len]; decide
  have hgd : gns.getD 0 0 = 0 := by decide +kernel
  exact reach_gens reach_gns Clo (hgd ▸ clo_gns 0 hlen)
    fun s hs u hu hP => clo_tvImg (gns_lt s hs) hu (clo_gns s hs) hP

theorem mfChkTvAdj_holds : mfChkTvAdj = true := by
  unfold mfChkTvAdj
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  intro k hk i hi
  obtain ⟨j, hj, hw, hm⟩ := clo_all k hk i hi
  rw [planeImg_wt hk hi hj hw, adjM_iff hi hj]
  refine ⟨hj, le_trans (four_le_ker (xorClosed_wMask (wData_lt hi)) (wMask_card hi)
    (tvPair k).2) (Finset.card_le_card fun x hx => ?_)⟩
  rw [Finset.mem_filter] at hx
  refine Finset.mem_inter.mpr ⟨hx.1, ?_⟩
  rw [hm]
  refine Finset.mem_image.mpr ⟨x, hx.1, ?_⟩
  rw [tvApply_eq_tvA]
  unfold tvA
  rw [if_neg (by rw [hx.2]; decide)]

end CertificateChecks.KernelSmithL6K
