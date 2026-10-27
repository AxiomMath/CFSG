module

public import Certificates.Kernel.J3T799350.InitChecks
public import Certificates.Kernel.SporSch.J3K426.Sift
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import CFSG.RankThree.PartTwo.Sec8.Hering611S4Init

public section

namespace CertificateChecks.KernelJ3T799350

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CertificateChecks.KernelSporSch
  CertificateChecks.KernelSpor CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore CFSG.RankThree.PartTwo.KFacts.K426
  CFSG.RankThree.PartTwo.Sec8.Hering611.J3T

theorem tab_eq {r : Nat} (hr : r < 19) : tabT (unpack 6156 13 (RT r)) = initTblOf r := by
  interval_cases r
  · rw [Nat.eq_of_beq_eq_true rt0, ← PJ3Check.arr_eq 0 (by norm_num)]
    simp [initTblOf, j3PGTbls, tabT]
  · rw [Nat.eq_of_beq_eq_true rt1, ← PJ3Check.arr_eq 1 (by norm_num)]
    simp [initTblOf, j3PGTbls, tabT]
  · rw [Nat.eq_of_beq_eq_true rt2, ← OddCore.j3CentTbl_eq (k := 0) (by norm_num), tabT_natArr]
    simp [initTblOf, j3OuterTbl]
  · rw [Nat.eq_of_beq_eq_true rt3, ← J3KT.hD (l := 0) (by norm_num)]
    simp [initTblOf, CFSG.RankThree.PartTwo.Sec8.Hering611.J3T.arrTbl, tabT]
  · rw [Nat.eq_of_beq_eq_true rt4, ← J3KT.hD (l := 1) (by norm_num)]
    simp [initTblOf, CFSG.RankThree.PartTwo.Sec8.Hering611.J3T.arrTbl, tabT]
  · rw [Nat.eq_of_beq_eq_true rt5, ← J3KT.hG]
    simp [initTblOf, CFSG.RankThree.PartTwo.Sec8.Hering611.J3T.arrTbl, tabT]
  · rw [Nat.eq_of_beq_eq_true rt6, ← OddCore.j3CentTbl_eq (k := 9) (by norm_num), tabT_natArr]
    simp [initTblOf]
  · rw [Nat.eq_of_beq_eq_true rt7, ← OddCore.j3CentTbl_eq (k := 10) (by norm_num), tabT_natArr]
    simp [initTblOf]
  · rw [Nat.eq_of_beq_eq_true rt8, ← OddCore.j3CentTbl_eq (k := 11) (by norm_num), tabT_natArr]
    simp [initTblOf]
  · rw [Nat.eq_of_beq_eq_true rt9, ← OddCore.j3CentTbl_eq (k := 12) (by norm_num), tabT_natArr]
    simp [initTblOf]
  · rw [Nat.eq_of_beq_eq_true rt10, ← OddCore.j3CentTbl_eq (k := 13) (by norm_num), tabT_natArr]
    simp [initTblOf]
  · rw [Nat.eq_of_beq_eq_true rt11, ← OddCore.j3CentTbl_eq (k := 14) (by norm_num), tabT_natArr]
    simp [initTblOf]
  · rw [Nat.eq_of_beq_eq_true rt12, ← J3KT.arr (k := 33) (by norm_num)]
    simp [initTblOf, CFSG.RankThree.PartTwo.Sec8.Hering611.J3T.arrTbl, tabT, j3tCAGens]
  · rw [Nat.eq_of_beq_eq_true rt13, ← J3KT.arr (k := 34) (by norm_num)]
    simp [initTblOf, CFSG.RankThree.PartTwo.Sec8.Hering611.J3T.arrTbl, tabT, j3tCAGens]
  · rw [Nat.eq_of_beq_eq_true rt14, ← J3KT.arr (k := 35) (by norm_num)]
    simp [initTblOf, CFSG.RankThree.PartTwo.Sec8.Hering611.J3T.arrTbl, tabT, j3tCAGens]
  · rw [Nat.eq_of_beq_eq_true rt15, ← J3KT.arr (k := 36) (by norm_num)]
    simp [initTblOf, CFSG.RankThree.PartTwo.Sec8.Hering611.J3T.arrTbl, tabT, j3tCAGens]
  · rw [Nat.eq_of_beq_eq_true rt16, ← J3KT.hX0]
    simp [initTblOf, CFSG.RankThree.PartTwo.Sec8.Hering611.J3T.arrTbl, tabT]
  · rw [Nat.eq_of_beq_eq_true rt17, ← J3KT.hU.1]
    simp [initTblOf, CFSG.RankThree.PartTwo.Sec8.Hering611.J3T.arrTbl, tabT]
  · rw [Nat.eq_of_beq_eq_true rt18, ← J3KT.hV.1]
    simp [initTblOf, CFSG.RankThree.PartTwo.Sec8.Hering611.J3T.arrTbl, tabT]


theorem rep_RT {r : Nat} (hr : r < 19) :
    CFSG.Sporadic.Th.Rep 6156 (tabT (unpack 6156 13 (RT r))) (initG r) := by
  rw [tab_eq hr]
  exact rep_initTblOf r

theorem initG_mem {r : Nat} (hr : r < 19) : initG r ∈ j3R := by
  rcases Nat.lt_or_ge r 3 with h3 | h3
  · interval_cases r
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp [initG]))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp [initG]))
    · exact Subgroup.mem_sup_right (by simpa [initG] using Subgroup.mem_zpowers j3u)
  · refine Subgroup.mem_sup_left ?_
    have hw : iwOK r = true := by
      rcases Nat.lt_or_ge r 11 with h11 | h11
      · simpa [Nat.add_sub_cancel' h3] using allBlk_spec iw0 (r - 3) (by omega)
      · simpa [Nat.add_sub_cancel' h11] using allBlk_spec iw1 (r - 11) (by omega)
    have hs := J3KT.sift_of hw
    have hc : canonK 6156 13 (mask 13) (6156 * 13) (RT r) = true := by
      simpa using allBlk_spec canon r (by omega)
    have hj : j3Sift (tabT (unpack 6156 13 (RT r))) = true := by
      unfold j3Sift
      rw [natArr_tabT hc]
      exact hs
    exact (j3_groupData.sift _ _ (rep_RT hr)).1 hj

end CertificateChecks.KernelJ3T799350

end
