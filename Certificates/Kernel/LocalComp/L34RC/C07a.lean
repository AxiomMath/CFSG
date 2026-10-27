module

public import Certificates.Kernel.LocalComp.L34RC.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34RC

theorem k07c0 : rc22207 0 15 = true := by quickRfl

theorem k07c1 : rc22207 15 15 = true := by quickRfl

theorem k07c2 : rc22207 30 15 = true := by quickRfl

end CertificateChecks.KernelLC.L34RC

end
