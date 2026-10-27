module

public import Certificates.Kernel.U43Pk.CovData
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kc_each CertificateChecks.KernelU43Pk.u43ClsBlk 0 16

#kc_each CertificateChecks.KernelU43Pk.u43PairBlk 0 48

#kc_each CertificateChecks.KernelU43Pk.u43ConjBlk 0 36

namespace CertificateChecks.KernelU43Pk

theorem repDig : repDigC = true := by quickRfl

end CertificateChecks.KernelU43Pk

end
