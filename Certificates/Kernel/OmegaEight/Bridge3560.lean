module

public import Certificates.Kernel.OmegaEight.Uniq3560PR
public import Certificates.Kernel.OmegaEight.Uniq3560MR
public import Certificates.Kernel.OmegaEight.Bridge3002
public import CFSG.Certificates.Kernel.O8N3Sound
public import CFSG.Certificates.Kernel.O8MinusSound
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitCUniqSADefs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitCUniqW

public noncomputable section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight.SplitC

theorem commSA_comm (SC a b : ℕ) : commSA SC a b = commSA SC b a := by
  unfold commSA
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact eq_comm

theorem commSA_self (SC a : ℕ) : commSA SC a a = true := by
  unfold commSA
  exact beq_self_eq_true _

section Plus

open CFSG.EvenSmallLie.OmegaEight

@[expose] def wUP : UniqWit where
  J := 38
  y := yIdx
  cl i := (invW i).1
  kind j := uKindP.getD j 2
  conj j := uConjP.getD j []
  dl j := uDlP.getD j []
  c0 := uC0P

theorem wUP_eq : wUP = wUPK := by
  unfold wUP wUPK uniqWitK
  congr 1
  · exact funext yIdx_eq
  · funext i
    rw [invW_eq]

theorem commP_eq : commP = commSA saCodes := by
  funext i k
  simp only [commP, commSA, saMat_eq, matMulK_eq]

theorem conjP_eq : conjP = conjSA saCodes := by
  funext c a w
  simp only [conjP, conjSA, saMat_eq, matMulK_eq]

theorem invP_eq : invP = invSA saCodes := by
  funext i
  simp only [invP, invSA, saMat_eq, matMulK_eq, idK_eq]

theorem uniqP : uniqCheckW 8192 commP conjP invP wUP = true := by
  rw [commP_eq, conjP_eq, invP_eq, wUP_eq]
  refine uniqCheckW_of_parts (List.all_eq_true.2 fun j hj => partsPK j (List.mem_range.1 hj))
    (fun j hj i hi => by
      by_cases hk : wUPK.kind j = 1
      · have hm := List.all_eq_true.1 kindPK j (List.mem_range.2 hj)
        simp only [hk, bne_self_eq_false, Bool.false_or, List.contains_iff_mem] at hm
        exact List.all_eq_true.1 (all_range_of_blocks (m := 8192) (s := 9) (nb := 16)
          (by norm_num) (rowsPK j hm)) i (List.mem_range.2 hi)
      · simp [dRowW, hk])
    (fun j hj t ht => List.all_eq_true.1 (all_range_of_blocks (m := 128) (s := 4) (nb := 8)
      (by norm_num) (pairsPK j hj)) t (List.mem_range.2 ht)) ?_ (commSA_comm _) (commSA_self _)
  rw [length_filter_range_blocks (s := 9) (nb := 16)
    (p := fun i => invSA saCodes i && decide (2 ≤ wUPK.kind (wUPK.cl i)))
    (C := fun b => [6, 6, 2, 3, 9, 1, 0, 1, 4, 5, 1, 0, 0, 9, 5, 3].getD b 0) (by norm_num) countPK]
  decide

end Plus

section Minus

open CFSG.EvenSmallLie.OmegaEightMinus

@[expose] def wUM : UniqWit where
  J := 36
  y := yIdx
  cl i := (invW i).1
  kind j := uKindM.getD j 2
  conj j := uConjM.getD j []
  dl j := uDlM.getD j []
  c0 := uC0M

theorem wUM_eq : wUM = wUMK := by
  unfold wUM wUMK uniqWitK
  congr 1
  · exact funext yIdx_eqM
  · funext i
    rw [invW_eqM]

theorem commM_eq : commM = commSA saCodes := by
  funext i k
  simp only [commM, commSA, saMat_eqM, matMulK_eq]

theorem conjM_eq : conjM = conjSA saCodes := by
  funext c a w
  simp only [conjM, conjSA, saMat_eqM, matMulK_eq]

theorem invM_eq : invM = invSA saCodes := by
  funext i
  simp only [invM, invSA, saMat_eqM, matMulK_eq, idK_eq]

theorem uniqM : uniqCheckW 8192 commM conjM invM wUM = true := by
  rw [commM_eq, conjM_eq, invM_eq, wUM_eq]
  refine uniqCheckW_of_parts (List.all_eq_true.2 fun j hj => partsMK j (List.mem_range.1 hj))
    (fun j hj i hi => by
      by_cases hk : wUMK.kind j = 1
      · have hm := List.all_eq_true.1 kindMK j (List.mem_range.2 hj)
        simp only [hk, bne_self_eq_false, Bool.false_or, List.contains_iff_mem] at hm
        exact List.all_eq_true.1 (all_range_of_blocks (m := 8192) (s := 9) (nb := 16)
          (by norm_num) (rowsMK j hm)) i (List.mem_range.2 hi)
      · simp [dRowW, hk])
    (fun j hj t ht => List.all_eq_true.1 (all_range_of_blocks (m := 128) (s := 4) (nb := 8)
      (by norm_num) (pairsMK j hj)) t (List.mem_range.2 ht)) ?_ (commSA_comm _) (commSA_self _)
  rw [length_filter_range_blocks (s := 9) (nb := 16)
    (p := fun i => invSA saCodes i && decide (2 ≤ wUMK.kind (wUMK.cl i)))
    (C := fun b => [3, 1, 7, 1, 0, 2, 6, 8, 1, 0, 1, 2, 13, 2, 4, 4].getD b 0) (by norm_num)
    countMK]
  decide

end Minus

end CertificateChecks.KernelO8
