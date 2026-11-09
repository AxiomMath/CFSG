module

public import Certificates.Kernel.OmegaEight.PlusW
public import CFSG.Certificates.Kernel.O8PhiImgSound
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.OmegaEight.Stage2.PlusW

theorem c_okP : cCheck wP = true := by
  simp only [cCheck, Bool.and_eq_true, beq_iff_eq]
  refine ⟨cE_ok, ?_⟩
  simp only [wP, decE_keys_size]
  decide +kernel

theorem tc_okP : tcCheck wP = true := by
  have hsC : sortedK (decE EnCP.D EnCP.m).keys = true := (Enum.of_enumOK cE_ok).2.1
  have hsT : sortedK (decE EnTP.D EnTP.m).keys = true := (Enum.of_enumOK tcE_ok).2.1
  simp only [tcCheck, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨tcE_ok, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [wP, decE_keys_size]
    decide +kernel
  · simp only [wP, gensIn, memK_decE_eq hsC (by decide +kernel), ← Array.all_toList]
    quickRfl
  · simp only [wP, centerCheck, commGens, mulK_eq, idK_eq, ← Array.all_toList, decE_toList]
    quickRfl
  · simp only [commGens, mulK_eq, ← Array.all_toList]
    quickRfl
  · simp only [commGens, mulK_eq, ← Array.all_toList]
    quickRfl
  · simp only [wP, memK_decE_eq hsT (by decide +kernel)]
    quickRfl

theorem u_okP : uCheck wP = true := by
  have hsT : sortedK (decE EnTP.D EnTP.m).keys = true := (Enum.of_enumOK tcE_ok).2.1
  simp only [uCheck, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨uE_ok, ?_⟩, ?_⟩, ?_⟩
  · simp only [wP, decE_keys_size]
    decide +kernel
  · simp only [wP, gensIn, memK_decE_eq hsT (by decide +kernel), ← Array.all_toList]
    quickRfl
  · simp only [wP, invFixCheckW, decE_keys_size, decE_getD, mulK_eq, idK_eq, fixLB,
      mulVecK_eq]
    quickRfl

theorem p3_okP : p3Check wP = true := by
  have hs2 : sortedK (decE EnC2.D EnC2.m).keys = true := (Enum.of_enumOK c2E_ok).2.1
  simp only [p3Check, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨p3E_ok, ?_⟩, ?_⟩
  · simp only [wP, decE_keys_size]
    decide +kernel
  · simp only [wP, gensIn, memK_decE_eq hs2 (by decide +kernel), ← Array.all_toList]
    quickRfl

theorem phi_okP : phiCheck wP = true := by
  have hi : imgCheckW phiK wP.imgX = true := by
    simp only [imgCheckW, mulVecK_eq, wP]
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

end CertificateChecks.KernelO8
