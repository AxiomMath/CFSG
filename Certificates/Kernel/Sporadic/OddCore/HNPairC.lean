module

public import Certificates.Kernel.Sporadic.OddCore.HNPairD
public meta import Certificates.Kernel.Sporadic.OddCore.HNPairD
public meta import Certificates.Kernel.Sporadic.RawGenSchOJ
public import Certificates.Kernel.Sporadic.RawGenSchOJ
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_data CertificateChecks.KernelSpor.HPD 1200 11 8 64
  CertificateChecks.KernelSpor.HNPair.sM
  CertificateChecks.KernelSpor.HNPair.bM 2 CertificateChecks.KernelSpor.HNPair.dD

#ks_rawchain_sl2_lv CertificateChecks.KernelSpor.HPD 0 0 19
#ks_rawchain_sl2_lv CertificateChecks.KernelSpor.HPD 1 0 19
#ks_rawchain_sl2_lv CertificateChecks.KernelSpor.HPD 2 0 19
#ks_rawchain_sl2_lv CertificateChecks.KernelSpor.HPD 3 0 19

#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.HPD 1 0 42
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.HPD 2 0 4
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.HPD 3 0 1

#ks_rawchain_sl2_osub CertificateChecks.KernelSpor.HPD
#ks_rawchain_sl2_scho CertificateChecks.KernelSpor.HPD 0 138

#ks_rawchain_sl2_joino CertificateChecks.KernelSpor.HPD

end
