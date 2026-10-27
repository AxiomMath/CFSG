module

public import Certificates.Kernel.Sporadic.M22Syl.Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.M22Syl

set_option maxRecDepth 100000

theorem c0 : chunkOK 0 = true := by quickRfl

theorem c1 : chunkOK 1 = true := by quickRfl

end CertificateChecks.KernelSpor.M22Syl

end
