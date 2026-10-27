module

public import Certificates.Kernel.LocalComp.F42.Chk20
public import Certificates.Kernel.LocalComp.BlockTac
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

theorem cchk20_0 : ∀ t < 21309, chk20 (0 + t) = true := by lc_cover 446

end CertificateChecks.KernelLC.F42

end
