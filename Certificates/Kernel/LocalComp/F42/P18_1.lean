module

public import Certificates.Kernel.LocalComp.F42.Chk18
public import Certificates.Kernel.LocalComp.BlockTac
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

theorem cchk18_1 : ∀ t < 4226, chk18 (17790 + t) = true := by lc_cover 183

end CertificateChecks.KernelLC.F42

end
