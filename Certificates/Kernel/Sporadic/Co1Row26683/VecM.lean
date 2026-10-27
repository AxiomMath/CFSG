module

public import Certificates.Kernel.Sporadic.Co1Row26683.DataM
public import Certificates.Kernel.Co1B.Vecs
public import Certificates.Data.Kernel.Co1BAct
public import Certificates.Data.Kernel.Spor.Mathieu
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.Co1Row26683

open CertificateChecks.KernelSpor CFSG.KC.Co1B CFSG.KS.Mathieu CFSG.KC.Enum

theorem ch26683V :
    bAnd(Nat.blt (nget C26683M.ZV (nat_lit 0)) (nat_lit 98280),
      Nat.beq (vAt CertificateChecks.KernelCo1B.CV.F (nget C26683M.ZV (nat_lit 0)))
        (nget C26683M.ZV (nat_lit 1))) = true := by
  quickRfl

end CertificateChecks.KernelSpor.Co1Row26683

end
