module

public import Certificates.Kernel.Sporadic.McLC.SylData
public import Certificates.Kernel.Sporadic.McLC.Defs
public import Certificates.Data.Kernel.Spor.CentReg
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.CentReg

theorem sqOne_ok : Nat.beq (cntN McLCS.cnt fun i =>
    Nat.beq (pcomp 275 9 (mask 9) (McLCS.T i) (McLCS.T i)) (pidn 275 9)) 36 = true := by
  quickRfl

end CertificateChecks.KernelSpor.McLC

end
