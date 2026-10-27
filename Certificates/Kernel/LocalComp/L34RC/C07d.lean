module

public import Certificates.Kernel.LocalComp.L34RC.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34RC

theorem k07c9 : rc22207 135 15 = true := by quickRfl

theorem k07c10 : rc22207 150 15 = true := by quickRfl

theorem k07c11 : rc22207 165 15 = true := by quickRfl

end CertificateChecks.KernelLC.L34RC

end
