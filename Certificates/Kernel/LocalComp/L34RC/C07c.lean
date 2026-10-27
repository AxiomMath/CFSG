module

public import Certificates.Kernel.LocalComp.L34RC.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34RC

theorem k07c6 : rc22207 90 15 = true := by quickRfl

theorem k07c7 : rc22207 105 15 = true := by quickRfl

theorem k07c8 : rc22207 120 15 = true := by quickRfl

end CertificateChecks.KernelLC.L34RC

end
