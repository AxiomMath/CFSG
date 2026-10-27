module

public import Certificates.Kernel.Sporadic.ONW.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kon_slices CertificateChecks.KernelSpor.ONW.chkS 80 120

namespace CertificateChecks.KernelSpor.ONW

theorem ne_ok : neOK = true := by quickRfl

end CertificateChecks.KernelSpor.ONW

end
