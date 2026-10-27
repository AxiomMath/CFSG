module

public import Certificates.Kernel.OmegaEight.PlusW
public import CFSG.Certificates.Kernel.O8PlusSound
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.OmegaEight.Stage2.PlusW

theorem sE4_ok : enumOK Plus.sGens4 wP.sE4 = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnS4.head
    EnS4.blocks
  rwa [genPairsK_eq (gs := Plus.sGens4)
    (by simp only [Plus.sGens4, slpGens, runK_eq, fpowK_eq]; decide +kernel)
    (by simp only [Plus.sGens4, slpGens, runK_eq, fpowK_eq]; decide +kernel)] at h

theorem s4_okP : sChk4 wP = true := by
  have hS : sortedK (decE EnS4.D EnS4.m).keys = true := (Enum.of_enumOK sE4_ok).2.1
  simp only [sChk4, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, sE4_ok⟩, ?_⟩, ?_⟩, ?_⟩, mE4_ok⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [gensOK, invPair, mulK_eq, idK_eq, ← Array.all_toList]
    quickRfl
  · simp only [gensOK, Plus.sGens4, slpGens, runK_eq, fpowK_eq, invPair, mulK_eq, idK_eq,
      ← Array.all_toList]
    quickRfl
  · simp only [wP, decE_keys_size]
    decide +kernel
  · simp only [wP, gensIn, memK_decE_eq hS (by decide +kernel), ← Array.all_toList]
    quickRfl
  · simp only [wP, oneClassCheckW, decE_keys_size, decE_getD, mulK_eq, idK_eq, fixLB,
      mulVecK_eq]
    quickRfl
  · simp only [wP, decE_keys_size]
    decide +kernel
  · simp only [wP, gensIn, memK_decE_eq hS (by decide +kernel), ← Array.all_toList]
    quickRfl
  · simp only [wP, contains_decE_eq]
    quickRfl

end CertificateChecks.KernelO8
