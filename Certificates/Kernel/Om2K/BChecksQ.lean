module

public import Certificates.Kernel.Om2K.BDefs
public meta import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

#kc_each CertificateChecks.KernelOm2.q80c 0 15
#kc_each CertificateChecks.KernelOm2.q82c 0 3

end
