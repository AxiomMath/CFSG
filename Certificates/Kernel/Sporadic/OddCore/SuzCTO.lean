module

public import Certificates.Kernel.Sporadic.OddCore.SuzCTS
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_each CertificateChecks.KernelSpor.SuzCT.DP CertificateChecks.KernelSpor.SuzCT.dSl 10
#kss_each CertificateChecks.KernelSpor.SuzCT.OP CertificateChecks.KernelSpor.SuzCT.oSl 10

namespace CertificateChecks.KernelSpor.SuzCT

theorem q_ok : qSl = true := by quickRfl

end CertificateChecks.KernelSpor.SuzCT

end
