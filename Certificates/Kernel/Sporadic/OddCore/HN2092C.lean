module

public import Certificates.Kernel.Sporadic.OddCore.HN2092D
public meta import Certificates.Kernel.Sporadic.OddCore.HN2092D
public meta import Certificates.Kernel.Sporadic.RawGenSchOJ
public import Certificates.Kernel.Sporadic.RawGenSchOJ
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_data CertificateChecks.KernelSpor.HSD 1100 11 8 64
  CertificateChecks.KernelSpor.HN2092.sM
  CertificateChecks.KernelSpor.HN2092.dBA 2 CertificateChecks.KernelSpor.HN2092.dD

#ks_rawchain_sl2_lv CertificateChecks.KernelSpor.HSD 0 0 18
#ks_rawchain_sl2_lv CertificateChecks.KernelSpor.HSD 1 0 18
#ks_rawchain_sl2_lv CertificateChecks.KernelSpor.HSD 2 0 18
#ks_rawchain_sl2_lv CertificateChecks.KernelSpor.HSD 3 0 18

#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.HSD 1 0 42
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.HSD 2 0 4
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.HSD 3 0 1

#ks_rawchain_sl2_osub CertificateChecks.KernelSpor.HSD
#ks_rawchain_sl2_scho CertificateChecks.KernelSpor.HSD 0 138

#ks_rawchain_sl2_joino CertificateChecks.KernelSpor.HSD

end
