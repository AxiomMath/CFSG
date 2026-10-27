module

public import Certificates.Kernel.Sporadic.Suz.EndData
public import Certificates.Kernel.Sporadic.RawGenSplitP
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_lvp CertificateChecks.KernelSpor.SuzEL 0 0 28
#ks_rawchain_sl2_lvp CertificateChecks.KernelSpor.SuzEL 1 0 28
#ks_rawchain_sl2_lvp CertificateChecks.KernelSpor.SuzES 0 0 28

end
