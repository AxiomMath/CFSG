module

public import Certificates.Kernel.Misc.Perm.HS100.SpChecks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.Sp

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.ConjOrb CFSG.KC.RightOrbBits
open CertificateChecks.KernelMisc.HS100

theorem orbCl : allN 3850 (closPtB 100 7 2 3850 C.SI OT OE) = true := by quickRfl

theorem orbTr : allN 3850 (treePt 2 3850 0 OE OD) = true := by quickRfl

end CertificateChecks.KernelMisc.HS100.Sp

end
