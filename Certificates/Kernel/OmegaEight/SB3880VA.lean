module

public import Certificates.Kernel.OmegaEight.SB3880V

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelO8.SB3880

theorem vBlockA : ∀ s < 4, (List.range' (8192 * s) 8192).all vAt = true := by
  intro s hs
  interval_cases s <;> decide +kernel

end CertificateChecks.KernelO8.SB3880

end
