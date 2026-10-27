module

public import Certificates.Kernel.OmegaEight.N3MChecksTR
public import CFSG.Certificates.Kernel.O8N3MSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Stage2
  CFSG.EvenSmallLie.OmegaEight.N3Split CFSG.EvenSmallLie.OmegaEight.N3Split.MinusW

set_option maxHeartbeats 0 in
theorem third_okN3M : thirdChk wN3M = true := by
  rw [thirdChk, Bool.and_eq_true]
  refine ⟨third_roots_okN3M, ?_⟩
  simp only [maxCheckW, burnCountL_eqM PnSW_eq, wN3M, decE_getD, decE_keys_size, mulK_eq,
    idK_eq, fixCountF_eqM PnSW_eq, commCount_eq]
  refine all_range_of_blocks (m := EnN3MS3.m) (s := 5) (nb := 16) (by decide +kernel)
    fun b hb => ?_
  interval_cases b <;> decide +kernel

end CertificateChecks.KernelO8
