module

public import Certificates.Kernel.G24Cls.Pack27203
public import Certificates.Kernel.G24Tri.Pack27206
public import Certificates.Data.Kernel.Spor.Prim
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelG24.Cls27203

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelG24.Tri27206

theorem kInvS : (invEqK 1365 11 (mask 11) (1365 * 11) (PK 6) (PK 6) &&
    invEqK 1365 11 (mask 11) (1365 * 11) (C35 0) (pcomp 1365 11 (mask 11) (C35 0) (C35 0)) &&
    invEqK 1365 11 (mask 11) (1365 * 11) (C35 1) (pcomp 1365 11 (mask 11) (C35 1)
      (pcomp 1365 11 (mask 11) (C35 1) (pcomp 1365 11 (mask 11) (C35 1) (C35 1))))) = true := by
  quickRfl

end CertificateChecks.KernelG24.Cls27203

end
