module

public import Certificates.Kernel.LocalComp.F42.Chk17
public import Certificates.Kernel.LocalComp.BlockTac
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

theorem cchk17_1 : ∀ t < 324, chk17 (16572 + t) = true := by lc_cover 67

end CertificateChecks.KernelLC.F42

end
