module

public import Certificates.Data.Kernel.F42Lev.L22
public import Certificates.Data.Kernel.F42Lev.Bfs
public import Certificates.Kernel.LocalComp.BlockTac
public import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42

theorem bfsAll : ∀ t < 48384, bfsChk L22 S D M Pt nL22 t = true := by lc_cover 64

end CertificateChecks.KernelLC.F42

end
