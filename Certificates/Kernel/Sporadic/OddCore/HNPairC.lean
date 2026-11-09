module

public import Certificates.Kernel.Sporadic.OddCore.HNPairD
public meta import Certificates.Kernel.Sporadic.OddCore.HNPairD
public meta import Certificates.Kernel.Sporadic.RawGenSchOJ
public import Certificates.Kernel.Sporadic.RawGenSchOJ
public meta import Certificates.Kernel.Sporadic.RawGenSchX
public import Certificates.Kernel.Sporadic.RawGenSchX
public import Certificates.Kernel.Sporadic.OddCore.HN2092C
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

theorem CertificateChecks.KernelSpor.HPD.agree :
    CFSG.KS.Raw.agreeDK 1100 11 (CFSG.KS.mask 11) CertificateChecks.KernelSpor.HPD.S
      CertificateChecks.KernelSpor.HPD.SI CertificateChecks.KernelSpor.HSD.S
      CertificateChecks.KernelSpor.HSD.SI 9 = true := by
  decide +kernel

theorem CertificateChecks.KernelSpor.HPD.faith :
    CFSG.KS.Raw.Orb.FaithK 1200 1100 11 CertificateChecks.KernelSpor.HPD.S
      CertificateChecks.KernelSpor.HPD.SI 9 4 CertificateChecks.KernelSpor.HPD.BP :=
  CFSG.KS.Raw.Orb.faithK_of_chain (NS := 138) (CH := 8)
    (CFSG.KS.Raw.Orb.binds_ofFn (by norm_num) (by norm_num) (by norm_num))
    CertificateChecks.KernelSpor.HSD.head CertificateChecks.KernelSpor.HSD.hl (by norm_num)
    CertificateChecks.KernelSpor.HSD.hs CertificateChecks.KernelSpor.HPD.agree (by norm_num)
    (by norm_num)

#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.HPD 1 0 42
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.HPD 2 0 4
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.HPD 3 0 1

#ks_rawchain_sl2_osub CertificateChecks.KernelSpor.HPD
#ks_rawchain_sl2_scho CertificateChecks.KernelSpor.HPD 0 138

#ks_rawchain_sl2_joino CertificateChecks.KernelSpor.HPD

end
