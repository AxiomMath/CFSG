module

public import Certificates.Kernel.Sporadic.Suz.EndChecks
public import Certificates.Kernel.Sporadic.Suz.EndChain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_each CertificateChecks.KernelSpor.SuzEndEl CertificateChecks.KernelSpor.SuzEnd.elemOK 64

end
