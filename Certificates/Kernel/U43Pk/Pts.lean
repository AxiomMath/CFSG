module

public import Certificates.Kernel.U43Pk.Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kc_each CertificateChecks.KernelU43Pk.u43PkBlk 0 16

namespace CertificateChecks.KernelU43Pk

theorem gens : gensC = true := by quickRfl

end CertificateChecks.KernelU43Pk

end
