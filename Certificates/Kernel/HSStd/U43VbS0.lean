module

public import Certificates.Kernel.HSStd.U43VbSolD
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

#kc_each CertificateChecks.KernelHSStd.U43Vb.ksCand 0 8

namespace CertificateChecks.KernelHSStd.U43Vb

open CFSG.KC.U43Case CertificateChecks.KernelHSStd

theorem ksCand_neg : (!(((List.range' 486 243).filter fun i =>
    candQ 820 10 (VbP 0) (VbP 1) (VbY.T i)) == [586])) = true := by
  quickRfl

end CertificateChecks.KernelHSStd.U43Vb

end
