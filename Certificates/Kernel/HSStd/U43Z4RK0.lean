module

public import Certificates.Kernel.HSStd.U43Z4RK
import CFSG.Certificates.Kernel.Common.Each
public import Certificates.Data.Kernel.Spor.MulHQ

public section

set_option maxRecDepth 400000
set_option Elab.async false

#kc_each CertificateChecks.KernelHSStd.U43Z4.peK 0 30
#kc_each CertificateChecks.KernelHSStd.U43Z4.hsK 0 8

end
