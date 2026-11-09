module

public import Certificates.Kernel.OmegaEight.Pi416101S

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelO8

theorem q8Part6 : q8Part (nat_lit 6) = true := by
  rw [q8Part_eqS]
  decide +kernel

end CertificateChecks.KernelO8

end
