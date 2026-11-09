module

public import Certificates.Kernel.OmegaEight.MinusCandBase
import CFSG.Certificates.Kernel.O8UnitSound

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight.Stage2

set_option maxHeartbeats 0 in
theorem candSys0 : ∀ b < 24, candSysM 0 b = true := by
  intro b hb
  rw [candSysM, Bool.and_eq_true]
  refine ⟨linCheckWith_of_P ?_, ?_⟩
  · simp only [Minus.cases, mulK_eq]
    interval_cases b <;> decide +kernel
  · interval_cases b <;> decide +kernel

end CertificateChecks.KernelO8
