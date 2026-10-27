module

public import Certificates.Kernel.Sporadic.ONNQ.Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kon_slices CertificateChecks.KernelSpor.ONNQ.nqCoS 0 8

namespace CertificateChecks.KernelSpor.ONNQ

theorem nqHead_ok : nqHead = true := by quickRfl

end CertificateChecks.KernelSpor.ONNQ

end
