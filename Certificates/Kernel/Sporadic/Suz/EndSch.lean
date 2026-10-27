module

public import Certificates.Kernel.Sporadic.Suz.EndData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.SuzEL 0 0 79
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.SuzEL 1 0 1
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.SuzES 0 0 16

end
