module

public import Certificates.Kernel.Sporadic.Fi22.Or9555Ck
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#kc_each CertificateChecks.KernelSpor.Or9555.or9555sk 0 16

public section

namespace CertificateChecks.KernelSpor.Or9555

theorem root : rootOK = true := by quickRfl

end CertificateChecks.KernelSpor.Or9555

end
