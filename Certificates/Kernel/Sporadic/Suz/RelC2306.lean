module

public import Certificates.Kernel.Sporadic.Suz.Imgs2306
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Suz2306

open CFSG.KC.Enum CFSG.KS.Pres

theorem r32 : Nat.beq (wordPK 1782 11 Gs GIs (CFSG.KBRoute.Suz.rels.getD 32 [])) (pidn 1782 11) = true := by quickRfl

end CertificateChecks.KernelSpor.Suz2306

end
