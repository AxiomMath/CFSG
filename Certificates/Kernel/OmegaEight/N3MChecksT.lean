module

public import Certificates.Kernel.OmegaEight.N3MW
public import Certificates.Kernel.OmegaEight.PnSWEq
public import CFSG.Certificates.Kernel.O8N3Sound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.O8MinusSound
public import CFSG.Certificates.Kernel.O8NodeSound

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Stage2
  CFSG.EvenSmallLie.OmegaEight.N3Split CFSG.EvenSmallLie.OmegaEight.N3Split.MinusW

set_option maxHeartbeats 0 in
theorem s3_okN3M : sChk3 wN3M = true := by
  have hS : sortedK (decE EnN3MS3.D EnN3MS3.m).keys = true := (Enum.of_enumOK sE3_okN3M).2.1
  simp only [sChk3, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, sE3_okN3M⟩, ?_⟩, ?_⟩, mE3_okN3M⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [gensOK, invPair, mulK_eq, idK_eq, ← Array.all_toList, N3Split.Minus.base,
      N3Split.Minus.cGens, N3Split.Minus.tGens, splitCGens, splitTGens, kronK_eq]
    quickRfl
  · simp only [gensOK, N3Split.Minus.sGens3, slpGens, runK_eq, fpowK_eq, invPair, mulK_eq,
      idK_eq, ← Array.all_toList, N3Split.Minus.base, N3Split.Minus.cGens, N3Split.Minus.tGens,
      splitCGens, splitTGens, kronK_eq]
    quickRfl
  · simp only [wN3M, decE_keys_size]
    decide +kernel
  · simp only [wN3M, gensIn, memK_decE_eq hS (by decide +kernel), ← Array.all_toList,
      N3Split.Minus.tGens, splitTGens, kronK_eq]
    quickRfl
  · simp only [wN3M, decE_keys_size]
    decide +kernel
  · simp only [wN3M, gensIn, memK_decE_eq hS (by decide +kernel), ← Array.all_toList]
    quickRfl
  · simp only [wN3M, avoidCheck, ← Array.all_toList]
    simp only [candB, fixCountF_eqM PnSW_eq, fixVecs_eq, commCount_eq, zfixCount, zfixOn,
      decE_toList, decE_getD, decE_keys_size, mulK_eq, mulVecK_eq, idK_eq, ← Array.all_toList,
      List.all_map]
    refine all_range_of_blocks (m := EnN3MM3.m) (s := 3) (nb := 32) (by decide +kernel)
      fun b hb => ?_
    interval_cases b <;> decide +kernel

end CertificateChecks.KernelO8
