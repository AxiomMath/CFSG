module

public import Certificates.Kernel.LocalComp.F42.Chk21
public import Certificates.Kernel.LocalComp.BlockTac
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

theorem cchk21_1 : ∀ t < 16387, chk21 (23707 + t) = true := by lc_cover 342

end CertificateChecks.KernelLC.F42

end
