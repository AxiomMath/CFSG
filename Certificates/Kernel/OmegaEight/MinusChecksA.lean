module

public import Certificates.Kernel.OmegaEight.MinusW
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
  simp only [phiCheck, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [fixCount_eq]
    decide +kernel
  · simp only [imgCheckW, mulVecK_eq, wM]
    quickRfl
  all_goals
    try simp only [invPair, commGens, mulK_eq, idK_eq, ← Array.all_toList]
    quickRfl

theorem c2_okM : c2Check wM = true := by
  have hsC : sortedK (decE EnCM.D EnCM.m).keys = true := (Enum.of_enumOK cE_okM).2.1
  have hs2 : sortedK (decE EnC2M.D EnC2M.m).keys = true := (Enum.of_enumOK c2E_okM).2.1
  simp only [c2Check, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨c2E_okM, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [wM, decE_keys_size]
    decide +kernel
  · simp only [wM, gensIn, memK_decE_eq hsC (by decide +kernel), ← Array.all_toList]
    quickRfl
  · simp only [commGens, mulK_eq, ← Array.all_toList]
    quickRfl
  · simp only [commGens, mulK_eq, ← Array.all_toList]
    quickRfl
  · simp only [wM, centInCheck, mulK_eq, memK_decE_eq hs2 (by decide +kernel),
      ← Array.all_toList, decE_toList]
    quickRfl

end CertificateChecks.KernelO8
