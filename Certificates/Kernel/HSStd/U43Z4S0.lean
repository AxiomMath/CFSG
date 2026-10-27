module

public import Certificates.Kernel.HSStd.U43Z4SolD
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

#kc_each CertificateChecks.KernelHSStd.U43Z4.ksCand 0 8

namespace CertificateChecks.KernelHSStd.U43Z4

open CFSG.KC.U43Case CertificateChecks.KernelHSStd

theorem ksCand_neg : (!(((List.range' 486 243).filter fun i =>
    candP 820 10 (Z4P 0) (Z4P 1) (Z4Y.T i)) == [586])) = true := by
  quickRfl

end CertificateChecks.KernelHSStd.U43Z4

end
