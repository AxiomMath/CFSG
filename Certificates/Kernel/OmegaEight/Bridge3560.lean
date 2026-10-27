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
    (fun j hj i hi => List.all_eq_true.1 (all_range_of_blocks (m := 8192) (s := 9) (nb := 16)
      (by norm_num) (rowsPK j hj)) i (List.mem_range.2 hi))
    (fun j hj t ht => List.all_eq_true.1 (all_range_of_blocks (m := 128) (s := 4) (nb := 8)
      (by norm_num) (pairsPK j hj)) t (List.mem_range.2 ht)) ?_
  rw [length_filter_range_blocks (s := 9) (nb := 16)
    (p := fun i => invSA saCodes i && decide (2 ≤ wUPK.kind (wUPK.cl i)))
    (C := fun b => [0, 3, 0, 3, 8, 1, 0, 0, 3, 5, 0, 0, 0, 3, 2, 3].getD b 0) (by norm_num) countPK]
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
    (fun j hj i hi => List.all_eq_true.1 (all_range_of_blocks (m := 8192) (s := 9) (nb := 16)
      (by norm_num) (rowsMK j hj)) i (List.mem_range.2 hi))
    (fun j hj t ht => List.all_eq_true.1 (all_range_of_blocks (m := 128) (s := 4) (nb := 8)
      (by norm_num) (pairsMK j hj)) t (List.mem_range.2 ht)) ?_
  rw [length_filter_range_blocks (s := 9) (nb := 16)
    (p := fun i => invSA saCodes i && decide (2 ≤ wUMK.kind (wUMK.cl i)))
    (C := fun b => [0, 0, 6, 1, 0, 2, 4, 7, 0, 0, 0, 0, 8, 0, 0, 3].getD b 0) (by norm_num) countMK]
  decide

end Minus

end CertificateChecks.KernelO8
