module

public import Certificates.Kernel.OmegaEight.MinusW
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.OmegaEight.Stage2.MinusW

theorem s0_okM : sChk0 wM = true := by
  have hS : sortedK (decE EnS0.D EnS0.m).keys = true := (Enum.of_enumOK sE0_okM).2.1
  simp only [sChk0, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, sE0_okM⟩, ?_⟩, ?_⟩, ?_⟩, mE0_okM⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [gensOK, invPair, mulK_eq, idK_eq, ← Array.all_toList]
    quickRfl
  · simp only [gensOK, Minus.sGens0, slpGens, runK_eq, fpowK_eq, invPair, mulK_eq, idK_eq,
      ← Array.all_toList]
    quickRfl
  · simp only [wM, decE_keys_size]
    decide +kernel
  · simp only [wM, gensIn, memK_decE_eq hS (by decide +kernel), ← Array.all_toList]
    quickRfl
  · simp only [wM, oneClassCheckW, decE_keys_size, decE_getD, mulK_eq, idK_eq, fixLB,
      mulVecK_eq]
    quickRfl
  · simp only [wM, decE_keys_size]
    decide +kernel
  · simp only [wM, gensIn, memK_decE_eq hS (by decide +kernel), ← Array.all_toList]
    quickRfl
  · simp only [wM, contains_decE_eq]
    quickRfl

theorem s1_okM : sChk1 wM = true := by
  have hS : sortedK (decE EnS1.D EnS1.m).keys = true := (Enum.of_enumOK sE1_okM).2.1
  simp only [sChk1, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, sE1_okM⟩, ?_⟩, ?_⟩, ?_⟩, mE1_okM⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [gensOK, invPair, mulK_eq, idK_eq, ← Array.all_toList]
    quickRfl
  · simp only [gensOK, Minus.sGens1, slpGens, runK_eq, fpowK_eq, invPair, mulK_eq, idK_eq,
      ← Array.all_toList]
    quickRfl
  · simp only [wM, decE_keys_size]
    decide +kernel
  · simp only [wM, gensIn, memK_decE_eq hS (by decide +kernel), ← Array.all_toList]
    quickRfl
  · simp only [wM, oneClassCheckW, decE_keys_size, decE_getD, mulK_eq, idK_eq, fixLB,
      mulVecK_eq]
    quickRfl
  · simp only [wM, decE_keys_size]
    decide +kernel
  · simp only [wM, gensIn, memK_decE_eq hS (by decide +kernel), ← Array.all_toList]
    quickRfl
  · simp only [wM, contains_decE_eq]
    quickRfl

end CertificateChecks.KernelO8
