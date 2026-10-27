module

public import Certificates.Data.Kernel.E6TT.Cover
public import Certificates.Kernel.E6TT.CoverData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelE6TT

theorem coverOK : CFSG.KC.E6TT.coverK C.CT = true := by quickRfl

end CertificateChecks.KernelE6TT

end
