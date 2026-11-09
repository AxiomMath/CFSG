module

public import Certificates.Kernel.SporSch.HeT.CntAFns
public import CFSG.Certificates.Kernel.SporSch.HeSrchPass
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HeCn

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch
open CertificateChecks.KernelSpor

theorem hePass598 : (!Nat.beq (srchPC 14 9 HeTb.NR HeTb.NR HeTb.LT HeTb.PT HeTb.QT HeC.LR (pmR HeCnRYA) 598)
    (srchPC 14 9 HeTb.NR HeTb.NR HeTb.LT HeTb.PT HeTb.QT HeC.LR (pmR HeCnRXA) 0)) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.HeCn

end
