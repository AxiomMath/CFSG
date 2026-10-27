module

public import Certificates.Kernel.LocalComp.F42.Chk17
public import Certificates.Kernel.LocalComp.BlockTac
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

theorem cchk17_0 : ∀ t < 16572, chk17 (0 + t) = true := by lc_cover 347

end CertificateChecks.KernelLC.F42

end
