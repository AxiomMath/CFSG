module

public import Certificates.Kernel.J4Pent.Defs
public import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Pent

theorem canon_ok : ∀ t < 6720, canonF t = true := by kc_cover 64

end CertificateChecks.KernelJ4Pent

end
