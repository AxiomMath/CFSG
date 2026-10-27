module

public import Certificates.Kernel.Sporadic.RawGenSchOJ
public meta import Certificates.Kernel.Sporadic.RawGenSchOJ
public import Certificates.Kernel.Sporadic.Fi24K.D2077
public meta import CFSG.Sporadic.FischerOddCore.Fi24R2KCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi24R

meta def pM : Array (Array Nat) := CFSG.Sporadic.FischerOddCore.fi24PStrong

meta def pB : Array Nat := CFSG.Sporadic.FischerOddCore.fi24PBase

end CertificateChecks.KernelSpor.Fi24R

#ks_rawchain_sl2_data CertificateChecks.KernelSpor.Fi24PC 378 9 16 64
  CertificateChecks.KernelSpor.Fi24R.pM CertificateChecks.KernelSpor.Fi24R.pB 2
  CertificateChecks.KernelSpor.Fi24W.pD

#ks_rawchain_sl2_lv CertificateChecks.KernelSpor.Fi24PC 0 0 6
#ks_rawchain_sl2_lv CertificateChecks.KernelSpor.Fi24PC 1 0 6
#ks_rawchain_sl2_lv CertificateChecks.KernelSpor.Fi24PC 2 0 6
#ks_rawchain_sl2_lv CertificateChecks.KernelSpor.Fi24PC 3 0 6

#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.Fi24PC 1 0 10
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.Fi24PC 2 0 4
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.Fi24PC 3 0 1

#ks_rawchain_sl2_osub CertificateChecks.KernelSpor.Fi24PC
#ks_rawchain_sl2_scho CertificateChecks.KernelSpor.Fi24PC 0 24

#ks_rawchain_sl2_joino CertificateChecks.KernelSpor.Fi24PC

end
