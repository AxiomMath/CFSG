module

public import Certificates.Kernel.J2Cover.K21
public import Certificates.Data.Kernel.J2EnumQ
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KC.J2Enum CFSG.KC.Child3

@[expose] noncomputable def fE5 (a : Nat) : Bool :=
  Nat.beq (blkCntQ 315 9 PA.LR PA.TR PA.BP (pidn 315 9) (PA.S 0) TA 5 5 2 a) 0

#lc_blocks E5B fE5 315 1

end CertificateChecks.KernelJ2Cover

end
