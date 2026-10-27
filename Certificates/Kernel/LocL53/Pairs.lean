module

public import Certificates.Kernel.LocL53.Data
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

#kc_each CertificateChecks.KernelLocL53.l53Pr 0 104

end
