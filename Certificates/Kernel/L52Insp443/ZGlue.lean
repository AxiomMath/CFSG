module

public import Certificates.Kernel.L52Insp443.PGlue
public import Certificates.Kernel.L52Insp443.SGlue
public import Certificates.Kernel.L52Insp443.CnGlue
public import CFSG.Certificates.Kernel.L52Insp443.Scan

public section

set_option maxRecDepth 20000

namespace CertificateChecks.KernelL52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.KC.L52I CFSG.SectionRank.QTK.Insp443.L52
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Literature.GL52 CFSG.Quasithin.KGC31.Native
  CFSG.SectionRank.QTK.Insp443.PermKit.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier

theorem range_getD {n w : ℕ} (hw : w < n) : (List.range n).getD w 0 = w := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_range]; exact hw), List.getElem_range]

theorem spZ_eq {z : ℕ} (hz : z < 7) :
    (e16.map (spanTabs 31)).getD z [] = spanTabs 31 (e16.getD z []) :=
  getD_map_lt e16 _ (by rw [show e16.length = 7 from rfl]; exact hz) [] []

theorem spW_eq {w : ℕ} (hw : w < 2) :
    ((List.range 2).map fun w => spanTabs 31 (wB w)).getD w [] = spanTabs 31 (wB w) := by
  rw [getD_map_lt _ _ (by rw [List.length_range]; exact hw) [] 0, range_getD hw]

theorem spA_eq {w : ℕ} (hw : w < 2) :
    ((List.range 2).map fun w => (aB w).map (spanTabs 31)).getD w [] =
      (aB w).map (spanTabs 31) := by
  rw [getD_map_lt _ _ (by rw [List.length_range]; exact hw) [] 0, range_getD hw]

theorem spA1_eq (w : ℕ) : ((aB w).map (spanTabs 31)).getD 1 [] = spanTabs 31 (e64a1.getD w []) := by
  have hl : 1 < (aB w).length := by
    rw [aB.eq_1]
    simp
  rw [getD_map_lt _ _ hl [] [], aB.eq_1]
  rfl

theorem cand_false (h : G) {T : Table} (hT : Rep 31 T (glPerm h)) {k : ℕ} (hk : k < 24) :
    ∀ t ∈ candTests (e16.map (spanTabs 31)) ((List.range 2).map fun w => spanTabs 31 (wB w))
      (x7Pairs (invT 31 x7T)) (cands7.getD k []) (kind7.getD k (3, 0, 0)), t T = false := by
  have hs := k1_sTest h hT
  intro t ht
  interval_cases k <;>
    simp only [kind7, List.getD_cons_zero, List.getD_cons_succ, candTests, List.mem_cons,
      List.not_mem_nil, or_false, if_true, if_false, reduceIte, Nat.reduceEqDiff] at ht
  · rcases ht with rfl | rfl
    · rw [spZ_eq (by norm_num), spW_eq (by norm_num)]
      exact hs.1
    · exact k1_c2Test (k := 0) (by norm_num) h hT
  · rcases ht with rfl | rfl
    · rw [spZ_eq (by norm_num), spW_eq (by norm_num)]
      exact hs.2.1
    · exact k1_c2Test (k := 1) (by norm_num) h hT
  · rcases ht with rfl | rfl
    · rw [spZ_eq (by norm_num), spW_eq (by norm_num)]
      exact hs.2.2.1
    · exact k1_c2Test (k := 2) (by norm_num) h hT
  · rcases ht with rfl | rfl
    · rw [spZ_eq (by norm_num), spW_eq (by norm_num)]
      exact hs.2.2.2.1
    · exact k1_c2Test (k := 3) (by norm_num) h hT
  · rcases ht with rfl | rfl
    · rw [spZ_eq (by norm_num), spW_eq (by norm_num)]
      exact hs.2.2.2.2.1
    · exact k1_c2Test (k := 4) (by norm_num) h hT
  · rcases ht with rfl | rfl
    · rw [spZ_eq (by norm_num), spW_eq (by norm_num)]
      exact hs.2.2.2.2.2
    · exact k1_c2Test (k := 5) (by norm_num) h hT
  all_goals
    subst ht
    rw [spW_eq (by norm_num)]
  · exact k2_centTest (k := 0) (by norm_num) h hT
  · exact k2_centTest (k := 1) (by norm_num) h hT
  · exact k2_centTest (k := 2) (by norm_num) h hT
  · exact k2_centTest (k := 3) (by norm_num) h hT
  · exact k2_centTest (k := 4) (by norm_num) h hT
  · exact k2_centTest (k := 5) (by norm_num) h hT
  · exact k2_centTest (k := 6) (by norm_num) h hT
  · exact k2_centTest (k := 7) (by norm_num) h hT
  · exact k2_centTest (k := 8) (by norm_num) h hT
  · exact k2_centTest (k := 9) (by norm_num) h hT
  · exact k2_centTest (k := 10) (by norm_num) h hT
  · exact k2_centTest (k := 11) (by norm_num) h hT

theorem tests52_false (h : G) {T : Table}
    (hT : Rep 31 T (glPerm h)) :
    ∀ t ∈ tests52 (e16.map (spanTabs 31)) ((List.range 2).map fun w => spanTabs 31 (wB w))
      ((List.range 2).map fun w => (aB w).map (spanTabs 31)) (x7Pairs (invT 31 x7T)),
      t T = false := by
  intro t ht
  rw [tests52.eq_1] at ht
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap] at ht
  rcases ht with ((⟨z, hz, rfl⟩ | ⟨w, hw, rfl⟩) | ⟨w, hw, rfl⟩) | ⟨k, hk, ht⟩
  · rw [spZ_eq hz]
    exact e16_centTest hz h hT
  · rw [spA_eq hw, spA1_eq, spW_eq hw]
    exact e64_cnTest hw h hT
  · rw [spA_eq hw, spW_eq hw]
    exact e64_perm3Test hw h hT
  · exact cand_false h hT hk t ht

theorem zero_count :
    countProducts 31 (anyTest (tests52 (e16.map (spanTabs 31))
      ((List.range 2).map fun w => spanTabs 31 (wB w))
      ((List.range 2).map fun w => (aB w).map (spanTabs 31)) (x7Pairs (invT 31 x7T))))
      (levelTables glCert) (idT 31) = 0 := by
  refine countProducts_eq_zero_of (by norm_num) glCert glCert_valid fun x T hT => ?_
  obtain ⟨h, hh⟩ := (mem_glCert_iff _).mp x.2
  rw [← hh] at hT
  unfold anyTest
  rw [← Bool.not_eq_true, List.any_eq_true]
  rintro ⟨t, ht, h1⟩
  rw [tests52_false h hT t ht] at h1
  exact Bool.false_ne_true h1

end CertificateChecks.KernelL52I

end
