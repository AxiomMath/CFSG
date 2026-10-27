module

public import Certificates.Kernel.Sporadic.SuzK.TabDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzK

set_option Elab.async false

theorem bfs_ok : bfsK = true := by quickRfl
theorem dep_ok : depK = true := by quickRfl
theorem cover_ok : coverK = true := by quickRfl

end CertificateChecks.KernelSpor.SuzK

end
