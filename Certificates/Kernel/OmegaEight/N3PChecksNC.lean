module

public import Certificates.Kernel.OmegaEight.N3PW
public import Certificates.Kernel.OmegaEight.PnSWEq
public import CFSG.Certificates.Kernel.O8N3Sound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.O8MinusSound
public import CFSG.Certificates.Kernel.O8NodeSound

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Stage2
  CFSG.EvenSmallLie.OmegaEight.N3Split CFSG.EvenSmallLie.OmegaEight.N3Split.PlusW

set_option maxHeartbeats 0 in
theorem nc_okN3P : ncChk wN3P = true := by
  have hsC : sortedK (decE EnN3PC.D EnN3PC.m).keys = true := (Enum.of_enumOK cE_okN3P).2.1
  have hmC : EnN3PC.m < 2 ^ 17 := by decide +kernel
  simp only [ncChk, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [wN3P, decE_getD, decE_keys_size, mulK_eq, idK_eq, fixCountF_eqM PnSW_eq]
    refine all_range_of_blocks (m := EnN3PC.m) (s := 12) (nb := 20) (by decide +kernel)
      fun b hb => ?_
    interval_cases b <;> decide +kernel
  · simp only [wN3P, invPair, mulK_eq, idK_eq, memK_decE_eq hsC hmC, fixCountF_eqM PnSW_eq]
    quickRfl
  · simp only [wN3P]
    rw [chainAux_eq _ _ (memK_decE_eq hsC hmC)]
    quickRfl
  · simp only [wN3P, linCheckWith, linRec, conPart_eq, commCons]
    quickRfl
  · simp only [wN3P, idK_eq]
    quickRfl
  · simp only [mulK_eq, idK_eq]
    decide +kernel
  · simp only [wN3P, memK_decE_eq hsC hmC]
    quickRfl

end CertificateChecks.KernelO8
