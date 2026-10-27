module

public import Certificates.Kernel.J4Pent.Defs
public import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Pent

theorem walk_ok : ∀ k < 5, walkF k = true := by kc_cover 1

end CertificateChecks.KernelJ4Pent

end
