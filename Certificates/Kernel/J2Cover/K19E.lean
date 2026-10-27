
module

public import Certificates.Kernel.J2Cover.EnumData
public import Certificates.Kernel.J2Cover.K21
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KC.J2Enum CFSG.KC.Child3

@[expose] noncomputable def fE0 (a : Nat) : Bool :=
  Nat.beq (blkCnt 315 9 PA.LR PA.TR PA.BP (pidn 315 9) (PA.S 0) TA a) (lget E0 a)

@[expose] noncomputable def fEU (a : Nat) : Bool :=
  Nat.beq (blkCntU 315 9 PA.LR PA.TR PA.BP OU a) (lget EU a)

#lc_blocks E0B fE0 315 1

#lc_blocks EUB fEU 315 1

end CertificateChecks.KernelJ2Cover

end
