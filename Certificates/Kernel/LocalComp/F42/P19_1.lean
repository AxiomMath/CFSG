module

public import Certificates.Kernel.LocalComp.F42.Chk19
public import Certificates.Kernel.LocalComp.BlockTac
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

theorem cchk19_1 : ∀ t < 12685, chk19 (19838 + t) = true := by lc_cover 265

end CertificateChecks.KernelLC.F42

end
