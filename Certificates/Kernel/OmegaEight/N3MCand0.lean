module

public import Certificates.Kernel.OmegaEight.N3MCandBase
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelO8

open CFSG.EvenSmallLie.OmegaEight.Stage2

set_option maxHeartbeats 0 in
theorem candN3M_0 :
    ∀ b < 24, spanAll (N3mLin 0 b).2.1 (N3mLin 0 b).2.2.length candPN3M = true := by
  intro b hb
  interval_cases b <;> decide +kernel

end CertificateChecks.KernelO8
