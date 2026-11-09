module

public import Certificates.Kernel.OmegaEight.MinusW
public import CFSG.Certificates.Kernel.O8CentOrbKSound
public import CFSG.Certificates.Kernel.O8PhiImgSound
public import Certificates.Kernel.OmegaEight.CentOrbData
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.OmegaEight.Stage2.MinusW

theorem c_okM : cCheck wM = true := by
  simp only [cCheck, Bool.and_eq_true, beq_iff_eq]
  refine ⟨cE_okM, ?_⟩
  simp only [wM, decE_keys_size]
  decide +kernel

theorem tc_okM : tcCheck wM = true := by
  have hsC : sortedK (decE EnCM.D EnCM.m).keys = true := (Enum.of_enumOK cE_okM).2.1
  have hsT : sortedK (decE EnTM.D EnTM.m).keys = true := (Enum.of_enumOK tcE_okM).2.1
  simp only [tcCheck, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨tcE_okM, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [wM, decE_keys_size]
    decide +kernel
  · simp only [wM, gensIn, memK_decE_eq hsC (by decide +kernel), ← Array.all_toList]
    quickRfl
  · simp only [wM, centerCheck, commGens, mulK_eq, idK_eq, ← Array.all_toList, decE_toList]
    quickRfl
  · simp only [commGens, mulK_eq, ← Array.all_toList]
    quickRfl
  · simp only [commGens, mulK_eq, ← Array.all_toList]
    quickRfl
  · simp only [wM, memK_decE_eq hsT (by decide +kernel)]
    quickRfl

theorem u_okM : uCheck wM = true := by
  have hsT : sortedK (decE EnTM.D EnTM.m).keys = true := (Enum.of_enumOK tcE_okM).2.1
  simp only [uCheck, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨uE_okM, ?_⟩, ?_⟩, ?_⟩
  · simp only [wM, decE_keys_size]
    decide +kernel
  · simp only [wM, gensIn, memK_decE_eq hsT (by decide +kernel), ← Array.all_toList]
    quickRfl
  · simp only [wM, invFixCheckW, decE_keys_size, decE_getD, mulK_eq, idK_eq, fixLB,
      mulVecK_eq]
    quickRfl

theorem p3_okM : p3Check wM = true := by
  have hs2 : sortedK (decE EnC2M.D EnC2M.m).keys = true := (Enum.of_enumOK c2E_okM).2.1
  simp only [p3Check, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨p3E_okM, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [wM, decE_keys_size]
    decide +kernel
  · simp only [wM, gensIn, memK_decE_eq hs2 (by decide +kernel), ← Array.all_toList]
    quickRfl
  · decide +kernel
  all_goals
    try simp only [mulK_eq, idK_eq]
    quickRfl

theorem phi_okM : phiCheck wM = true := by
  have hi : imgCheckW phiK wM.imgX = true := by
    simp only [imgCheckW, mulVecK_eq, wM]
    quickRfl
  have hinv : invPair phiK phiK = true := by
    simp only [invPair, mulK_eq, idK_eq]
    quickRfl
  simp only [phiCheck, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, hi⟩, hinv⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [fixCount_eq_of_imgCheckW hinv hi]
    decide
  all_goals
    try simp only [commGens, mulK_eq, idK_eq, ← Array.all_toList]
    quickRfl

theorem c2_okM : c2Check wM = true := by
  have hsC : sortedK (decE EnCM.D EnCM.m).keys = true := (Enum.of_enumOK cE_okM).2.1
  have hin : gensIn Minus.c2Gens wM.cE = true := by
    simp only [wM, gensIn, memK_decE_eq hsC (by decide +kernel), ← Array.all_toList]
    quickRfl
  have hcb : commGens Minus.c2Gens Minus.bK = true := by
    simp only [commGens, mulK_eq, ← Array.all_toList]
    quickRfl
  have ho : orbCertK wM.cE Minus.bK orbRsM orbCsM = true := by
    simp only [wM, orbCertK, mulK_eq, memK_decE_eq hsC (by decide +kernel)]
    decide +kernel
  have hbb : invPair Minus.bK Minus.bK = true := by
    simp only [invPair, mulK_eq, idK_eq]
    quickRfl
  simp only [c2Check, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨c2E_okM, ?_⟩, hin⟩, ?_⟩, hcb⟩,
    centInCheck_of_orbCertK cE_okM c2E_okM ?_ hbb hin hcb ho ?_⟩
  · simp only [wM, decE_keys_size]
    decide +kernel
  · simp only [commGens, mulK_eq, ← Array.all_toList]
    quickRfl
  · simp only [wM, decE_keys_size]
    decide +kernel
  · simp only [wM, decE_keys_size]
    decide +kernel

end CertificateChecks.KernelO8
