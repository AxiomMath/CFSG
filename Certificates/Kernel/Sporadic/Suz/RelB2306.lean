module

public import Certificates.Kernel.Sporadic.Suz.Imgs2306
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Suz2306

open CFSG.KC.Enum CFSG.KS.Pres

theorem r30 : Nat.beq (wordPK 1782 11 Gs GIs (CFSG.KBRoute.Suz.rels.getD 30 [])) (pidn 1782 11) = true := by quickRfl
theorem r31 : Nat.beq (wordPK 1782 11 Gs GIs (CFSG.KBRoute.Suz.rels.getD 31 [])) (pidn 1782 11) = true := by quickRfl
theorem r33 : Nat.beq (wordPK 1782 11 Gs GIs (CFSG.KBRoute.Suz.rels.getD 33 [])) (pidn 1782 11) = true := by quickRfl

end CertificateChecks.KernelSpor.Suz2306

end
