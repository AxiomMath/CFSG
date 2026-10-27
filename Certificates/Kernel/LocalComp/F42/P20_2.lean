module

public import Certificates.Kernel.LocalComp.F42.Chk20
public import Certificates.Kernel.LocalComp.BlockTac
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

theorem cchk20_2 : ∀ t < 8416, chk20 (35104 + t) = true := by lc_cover 185

end CertificateChecks.KernelLC.F42

end
