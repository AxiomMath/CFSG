module

public import Certificates.Kernel.SmithL6K.GlueW
public import Certificates.Kernel.SmithL6K.GlueP
public import Certificates.Kernel.SmithL6K.ChecksPr
public import CFSG.Certificates.Kernel.SmithL6KPrSound

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K CFSG.SmithL6.Kernel
open CFSG.SmithE (applyCols)

theorem formInv_gns : ∀ s < gns.length, FormInv (gns.getD s 0) := by
  intro s hs
  have h := formG_ok
  unfold formGK at h
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have hg := gns_lt s hs
  refine formInv_of_basis fun a ha b hb => ?_
  rw [cols_getD hg ha, cols_getD hg hb]
  exact h _ (by rw [getD_of_lt hs]; exact List.getElem_mem hs) a ha b hb

theorem row_facts : ∀ s < gns.length, ∀ i < 1395, fldW 11 (gpP.getD s 0) i < 1395 ∧
    wt (fldW 11 (gpP.getD s 0) i) = applyCols (tvCols (gns.getD s 0)) (wt i) ∧
    setM (wMask (fldW 11 (gpP.getD s 0) i)) = (setM (wMask i)).image (tvApply (gns.getD s 0)) := by
  intro s hs
  have hg := gns_lt s hs
  have h := close_rows s (by rw [gns_len] at hs; exact hs)
  rw [← tvCols_eq hg, fld_tcP hg] at h
  exact closeRow_facts hg (fun _ hi => wtP_eq hi) (fun _ hi => wmP_eq hi) h

theorem reach_planes : Reach 1395 gns.length (· == 0)
    (fun s u v => fldW 11 (gpP.getD s 0) u == v) := by
  have h6 : gns.length = 6 := gns_len
  refine Reach.mono (m := 6) (reach_of_treeK ptr_ok) fun s hs u _ v _ he =>
    ⟨s, by rw [h6]; exact hs, ?_⟩
  unfold pEdgeK at he
  exact he

theorem testBit_zero_wMask {i : Nat} (hi : i < 1395) : (wMask i).testBit 0 = true :=
  (mem_setM.mp (xorClosed_wMask (wData_lt hi)).2.1).2

theorem opp_all : ∀ i < 1395, ∀ j < 1395,
    fB (wt i) (wt j) = decide ((setM (wMask i) ∩ setM (wMask j)).card = 1) := by
  refine opp_of_reach gns_lt (fun s hs i hi => (row_facts s hs i hi).1)
    (fun s hs i hi => (row_facts s hs i hi).2.1) (fun s hs i hi => (row_facts s hs i hi).2.2)
    formInv_gns wt_inj reach_planes ?_
  intro j hj
  have h := row0_ok
  unfold row0K at h
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have e := h j hj
  rw [wtP_eq (by decide), wtP_eq hj, wmP_eq (by decide), wmP_eq hj] at e
  rw [e, ← setM_and]
  have h0 : (wMask 0 &&& wMask j).testBit 0 = true := by
    rw [Nat.testBit_and, testBit_zero_wMask (by decide), testBit_zero_wMask hj]
    rfl
  exact beq_one_iff (inter_facts (by decide) hj).1 h0

theorem wMask_inj {i j : Nat} (hi : i < 1395) (hj : j < 1395) (e : wMask i = wMask j) : i = j := by
  have hn := (CFSG.Decide.nodup_of_bitsetNodup_nat wmk_nodup).of_map
  rw [wMask_eq hi, wMask_eq hj, getD_of_lt (by rw [wmk_length]; exact hi),
    getD_of_lt (by rw [wmk_length]; exact hj)] at e
  exact (List.Nodup.getElem_inj_iff hn).mp e

theorem pairs_holds : chkPairs = true := by
  unfold chkPairs
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq]
  intro i hi j hj
  have hadj : adjM i j = decide (4 ≤ (setM (wMask i &&& wMask j)).card) := by
    unfold adjM
    rw [maskArr_get hi, maskArr_get hj]
    exact Bool.eq_iff_iff.mpr ((atLeast4_iff (inter_facts hi hj).1).trans decide_eq_true_iff.symm)
  rw [wtArr_get hi, wtArr_get hj, opp_all i hi j hj, hadj, meetCard_formula hi hj, ← setM_and]
  obtain ⟨-, hX, h8⟩ := inter_facts hi hj
  by_cases hij : i = j
  · subst hij
    rw [Nat.and_self, wMask_card hi, if_pos rfl]
    decide
  · have hne : (setM (wMask i &&& wMask j)).card ≠ 8 := by
      intro h
      rw [setM_and] at h
      have e1 : setM (wMask i) ∩ setM (wMask j) = setM (wMask i) :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [h, wMask_card hi])
      have e2 : setM (wMask i) ∩ setM (wMask j) = setM (wMask j) :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [h, wMask_card hj])
      exact hij (wMask_inj hi hj (eq_of_setM_eq (wMask_lt hi) (wMask_lt hj) (e1.symm.trans e2)))
    rw [if_neg hij]
    rcases card_pow2 hX h8 with h | h | h | h
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · exact absurd h hne

end CertificateChecks.KernelSmithL6K
