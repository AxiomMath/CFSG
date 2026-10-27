module

public import Certificates.Kernel.LocalComp.L34RC.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34RC

theorem k07c3 : rc22207 45 15 = true := by quickRfl

theorem k07c4 : rc22207 60 15 = true := by quickRfl

theorem k07c5 : rc22207 75 15 = true := by quickRfl

end CertificateChecks.KernelLC.L34RC

end
