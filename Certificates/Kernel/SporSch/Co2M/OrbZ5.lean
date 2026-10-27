module

public import Certificates.Kernel.SporSch.Co2M.OrbZK
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSporSch.Co2M

theorem oz5 : ∀ t < 7168, ozK (Nat.add 35840 t) = true := by
  kc_cover 32

end CertificateChecks.KernelSporSch.Co2M

end
