module

public import Certificates.Kernel.Sporadic.PSp45.Data
public import Certificates.Data.Kernel.Spor.MCount
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelSpor.PSp45

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.MEnum CFSG.KS.SporSch.MOC

set_option maxRecDepth 400000

example : (!headK 45 6 (mask 6) (45 * 6) (pidn 45 6) P45Q.S P45Q.SI 8 2 wordsA 4 P45Q.BP) =
    true := by quickRfl

example : (!allC (clsOneR 45 6 tX tY 3 1000) P45CL) = true := by quickRfl

example : (!clsDisj 45 6 (P45CL ++ P45CL)) = true := by quickRfl

example : (!Nat.beq (cntOrdK 45 6 (mask 6) (45 * 6) (pidn 45 6) P45Q.LR P45Q.TR 4 One 3 0)
    (P45X.CS.getD 0 0)) = true := by quickRfl

example : (!CFSG.KS.M11.ordIs 45 6 (mask 6) (pidn 45 6) One (2 - 1)) = true := by quickRfl

example : (!CFSG.KS.M11.ordIs 45 6 (mask 6) (pidn 45 6) (P45Q.S 0) (5 - 1)) = true := by
  quickRfl

end CertificateChecks.KernelSpor.PSp45
