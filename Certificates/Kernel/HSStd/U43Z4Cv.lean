module

public import Certificates.Kernel.HSStd.U43Z4Data
public import Certificates.Data.Kernel.U43Case
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertificateChecks.KernelHSStd.U43Z4

open CFSG.KC.Enum CFSG.KS CFSG.KC.U43Case CertificateChecks.KernelHSStd

@[expose] noncomputable def cv (s : Nat) : Bool :=
  coverP 820 10 Z4C.cnt Z4C.T Z4CY.cnt Z4CY.T Z4W (Nat.mul 360 s) 360

end CertificateChecks.KernelHSStd.U43Z4

#kc_each CertificateChecks.KernelHSStd.U43Z4.cv 0 8

end
