module

public import Certificates.Kernel.LocalComp.F42.Chk19
public import Certificates.Kernel.LocalComp.BlockTac
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

theorem cchk19_0 : ∀ t < 19838, chk19 (0 + t) = true := by lc_cover 416

end CertificateChecks.KernelLC.F42

end
