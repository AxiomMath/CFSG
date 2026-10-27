module

public import Certificates.Kernel.Sporadic.M22Syl.Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.M22Syl

set_option maxRecDepth 100000

theorem c4 : chunkOK 4 = true := by quickRfl

theorem c5 : chunkOK 5 = true := by quickRfl

end CertificateChecks.KernelSpor.M22Syl

end
