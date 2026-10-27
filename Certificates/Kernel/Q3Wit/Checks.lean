module

public import Certificates.Data.Kernel.Misc.WitK
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Kernel.J2Cover.AutChains
public import Certificates.Kernel.Census.J2H.Chains
public import Certificates.Kernel.SchreierFam.J3Cq
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelQ3Wit

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.ArrEnum CFSG.KC.WitK
open CertificateChecks.KernelJ2Cover CertificateChecks.KernelJ2H
  CertificateChecks.KernelSchreierFam.J3Cq

theorem j2Perm :
    (permB 315 9 (C2A.S 0) && permB 315 9 (C2A.S 1) && permB 315 9 (S0C.S 0)) = true := by
  quickRfl

theorem j2Wit : witK 315 9
    (pcomp 315 9 (mask 9) (pcomp 315 9 (mask 9) (C2A.S 0) (C2A.S 1))
      (pcomp 315 9 (mask 9) (C2A.S 0) (C2A.S 1)))
    (pcomp 315 9 (mask 9) (pcomp 315 9 (mask 9) (C2A.S 1) (C2A.S 0))
      (pcomp 315 9 (mask 9) (C2A.S 1) (C2A.S 0)))
    (S0C.S 0) = true := by
  quickRfl

theorem j3Wit : witK 20520 15 (pcomp 20520 15 (mask 15) (KK 0) (KK 1))
    (pcomp 20520 15 (mask 15) (KK 1) (pcomp 20520 15 (mask 15) (KK 0)
      (pcomp 20520 15 (mask 15) (KK 0) (pcomp 20520 15 (mask 15) (KK 1)
        (pcomp 20520 15 (mask 15) (KK 1) (pcomp 20520 15 (mask 15) (KK 0)
          (pcomp 20520 15 (mask 15) (KK 1) (KK 0))))))))
    (AB 0) = true := by
  quickRfl

end CertificateChecks.KernelQ3Wit

end
