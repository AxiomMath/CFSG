module

public import Certificates.Kernel.OmegaEight.MinusCandBase

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight.Stage2

set_option maxHeartbeats 0 in
theorem candSys0 : ∀ b < 24, candSysM 0 b = true := by
  intro b hb
  simp only [candSysM, linCheckWith, linRec, conPart_eq, Minus.cases, mulK_eq]
  interval_cases b <;> decide +kernel

end CertificateChecks.KernelO8
