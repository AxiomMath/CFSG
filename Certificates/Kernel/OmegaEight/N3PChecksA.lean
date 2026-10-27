module

public import Certificates.Kernel.OmegaEight.N3PW
public import CFSG.Certificates.Kernel.O8N3Sound
public import Certificates.Kernel.OmegaEight.PnSWEq
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.O8MinusSound
public import CFSG.Certificates.Kernel.O8NodeSound

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Stage2
  CFSG.EvenSmallLie.OmegaEight.N3Split
  CFSG.EvenSmallLie.OmegaEight.N3Split.PlusW

theorem c_okN3P : cCheck wN3P = true := by
  simp only [cCheck, Bool.and_eq_true, beq_iff_eq]
  refine ⟨cE_okN3P, ?_⟩
  simp only [wN3P, decE_keys_size]
  decide +kernel

theorem tc_okN3P : tcCheck wN3P = true := by
  have hsC : sortedK (decE EnN3PC.D EnN3PC.m).keys = true := (Enum.of_enumOK cE_okN3P).2.1
  have hsT : sortedK (decE EnN3PT.D EnN3PT.m).keys = true := (Enum.of_enumOK tcE_okN3P).2.1
  simp only [tcCheck, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨tcE_okN3P, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [wN3P, decE_keys_size]
    decide +kernel
  · simp only [wN3P, gensIn, memK_decE_eq hsC (by decide +kernel), ← Array.all_toList,
      N3Split.Plus.tGens, splitTGens, kronK_eq]
    quickRfl
  · simp only [wN3P, centerCheck, commGens, mulK_eq, idK_eq, ← Array.all_toList, decE_toList,
      N3Split.Plus.tGens, splitTGens, kronK_eq]
    quickRfl
  · simp only [commGens, mulK_eq, ← Array.all_toList, N3Split.Plus.tGens, splitTGens, kronK_eq]
    quickRfl
  · simp only [commGens, mulK_eq, ← Array.all_toList, N3Split.Plus.tGens, splitTGens, kronK_eq]
    quickRfl
  · simp only [wN3P, memK_decE_eq hsT (by decide +kernel)]
    quickRfl

set_option maxHeartbeats 0 in
theorem uk_okN3P : ukCheck wN3P = true := by
  have hsT : sortedK (decE EnN3PT.D EnN3PT.m).keys = true := (Enum.of_enumOK tcE_okN3P).2.1
  simp only [ukCheck, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨ukE_okN3P, ?_⟩, ?_⟩, ?_⟩
  · simp only [wN3P, decE_keys_size]
    decide +kernel
  · simp only [wN3P, gensIn, memK_decE_eq hsT (by decide +kernel), ← Array.all_toList,
      N3Split.Plus.ukGens, N3Split.Plus.tGens, splitTGens, kronK_eq]
    quickRfl
  · simp only [wN3P, avoidCheck, ← Array.all_toList]
    simp only [candB, fixCountF_eqM PnSW_eq, fixVecs_eq, commCount_eq, zfixCount, zfixOn,
      decE_toList, decE_getD, decE_keys_size, mulK_eq, mulVecK_eq, idK_eq, ← Array.all_toList,
      List.all_map]
    refine all_range_of_blocks (m := EnN3PUK.m) (s := 3) (nb := 16) (by decide +kernel)
      fun b hb => ?_
    interval_cases b <;> decide +kernel

theorem phi_okN3P : phiCheck wN3P = true := by
  simp only [phiCheck, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [fixCount_eq]
    decide +kernel
  · simp only [imgCheckW, mulVecK_eq, wN3P]
    quickRfl
  all_goals
    try simp only [invPair, commGens, mulK_eq, idK_eq, ← Array.all_toList, N3Split.Plus.cGens,
      splitCGens, kronK_eq]
    quickRfl

theorem p3_okN3P : p3Check wN3P = true := by
  have hs2 : sortedK (decE EnN3PC2.D EnN3PC2.m).keys = true := (Enum.of_enumOK c2E_okN3P).2.1
  simp only [p3Check, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨p3E_okN3P, ?_⟩, ?_⟩
  · simp only [wN3P, decE_keys_size]
    decide +kernel
  · simp only [wN3P, gensIn, memK_decE_eq hs2 (by decide +kernel), ← Array.all_toList]
    quickRfl

set_option maxHeartbeats 0 in
theorem c2_okN3P : c2Check wN3P = true := by
  have hsC : sortedK (decE EnN3PC.D EnN3PC.m).keys = true := (Enum.of_enumOK cE_okN3P).2.1
  have hs2 : sortedK (decE EnN3PC2.D EnN3PC2.m).keys = true := (Enum.of_enumOK c2E_okN3P).2.1
  simp only [c2Check, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨c2E_okN3P, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [wN3P, decE_keys_size]
    decide +kernel
  · simp only [wN3P, gensIn, memK_decE_eq hsC (by decide +kernel), ← Array.all_toList]
    quickRfl
  · simp only [commGens, mulK_eq, ← Array.all_toList]
    quickRfl
  · simp only [commGens, mulK_eq, ← Array.all_toList]
    quickRfl
  · simp only [wN3P, centInCheck, mulK_eq, memK_decE_eq hs2 (by decide +kernel),
      ← Array.all_toList, decE_toList, List.all_map]
    refine all_range_of_blocks (m := EnN3PC.m) (s := 12) (nb := 20) (by decide +kernel)
      fun b hb => ?_
    interval_cases b <;> decide +kernel
  · simp only [wN3P, fpowK_eq, idK_eq, ← Array.all_toList, decE_toList]
    quickRfl

end CertificateChecks.KernelO8
