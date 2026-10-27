module

public import Certificates.Kernel.J4M4.Defs
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4M4

theorem headK_ok : headK = true := by decide +kernel

#kc_each CertificateChecks.KernelJ4M4.layK 0 10

end CertificateChecks.KernelJ4M4
