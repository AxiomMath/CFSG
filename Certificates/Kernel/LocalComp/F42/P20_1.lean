module

public import Certificates.Kernel.LocalComp.F42.Chk20
public import Certificates.Kernel.LocalComp.BlockTac
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

theorem cchk20_1 : ∀ t < 13795, chk20 (21309 + t) = true := by lc_cover 290

end CertificateChecks.KernelLC.F42

end
