module

public import Certificates.Kernel.Misc.Perm.HS100.SpChecks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.Sp

open CFSG.KC.Enum CFSG.KS CFSG.KC.BfsPin

theorem orbKeys : distinctK 3850 OT OS = true := by quickRfl

end CertificateChecks.KernelMisc.HS100.Sp

end
