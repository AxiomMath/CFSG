module

public import Certificates.Kernel.LocalComp.L34SOData
public import Certificates.Kernel.LocalComp.L34RData
public import Certificates.Data.Kernel.S1277K589102
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC

open CFSG.KC.L34K CertificateChecks.KernelLC.L34X
open CFSG.KLie.CT (notB)

theorem k589102orb :
    orbK 42 6 3 L34R.G GI L34SO.T L34SO.E L34SO.S L34SO.SI 315 11 (RP 0) = true := by quickRfl

theorem k589102cls : clsK 42 6 64 L34C1.P 16 K589E1.T K589E2.T = true := by quickRfl

end CertificateChecks.KernelLC

end
