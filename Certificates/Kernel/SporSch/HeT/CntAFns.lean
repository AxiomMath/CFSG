module

public import Certificates.Kernel.SporSch.HeT.CntData
public import Certificates.Data.Kernel.SporSch.HeSrchK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HeCn

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch
open CertificateChecks.KernelSpor

@[expose] noncomputable def srAH (i : Nat) : Bool :=
  Nat.beq (srchAK 14 9 HeTb.NR HeTb.NR HeTb.LT HeTb.PT HeTb.QT HeC.LR
    CFSG.Sporadic.HeldB.heBase 0 (pmR HeCnRXA) (pmR HeCnRYA) 598 (Nat.mul i 280) 280) 0

end CertificateChecks.KernelSporSch.HeCn

#kss_each CertificateChecks.KernelSporSch.HeCn.CA CertificateChecks.KernelSporSch.HeCn.cjA 49

end
