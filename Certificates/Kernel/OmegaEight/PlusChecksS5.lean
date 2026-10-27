module

public import Certificates.Kernel.OmegaEight.PlusW
public import CFSG.Certificates.Kernel.O8PlusSound
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.OmegaEight.Stage2.PlusW

theorem sE5_ok : enumOK Plus.sGens5 wP.sE5 = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnS5.head
    EnS5.blocks
  rwa [genPairsK_eq (gs := Plus.sGens5)
    (by simp only [Plus.sGens5, slpGens, runK_eq, fpowK_eq]; decide +kernel)
    (by simp only [Plus.sGens5, slpGens, runK_eq, fpowK_eq]; decide +kernel)] at h

theorem s5_okP : sChk5 wP = true := by
  have hS : sortedK (decE EnS5.D EnS5.m).keys = true := (Enum.of_enumOK sE5_ok).2.1
  simp only [sChk5, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, sE5_ok⟩, ?_⟩, ?_⟩, ?_⟩, mE5_ok⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [gensOK, invPair, mulK_eq, idK_eq, ← Array.all_toList]
    quickRfl
  · simp only [gensOK, Plus.sGens5, slpGens, runK_eq, fpowK_eq, invPair, mulK_eq, idK_eq,
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
