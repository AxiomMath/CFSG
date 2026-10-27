module

public import Certificates.Kernel.Misc.RuInv.Data
public import Certificates.Data.Kernel.Misc.RuInv
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelMisc.RuInv

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.RuInv

theorem permA0 : permOK 4060 12 (mask 12) (4060 * 12) AD.n0 (invP AD.n0) = true := by quickRfl

theorem permA1 : permOK 4060 12 (mask 12) (4060 * 12) AD.n1 (invP AD.n1) = true := by quickRfl

end CertificateChecks.KernelMisc.RuInv

end
