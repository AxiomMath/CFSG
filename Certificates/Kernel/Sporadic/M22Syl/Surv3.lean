module

public import Certificates.Kernel.Sporadic.M22Syl.Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.M22Syl

set_option maxRecDepth 100000

theorem c6 : chunkOK 6 = true := by quickRfl

theorem c7 : chunkOK 7 = true := by quickRfl

end CertificateChecks.KernelSpor.M22Syl

end
