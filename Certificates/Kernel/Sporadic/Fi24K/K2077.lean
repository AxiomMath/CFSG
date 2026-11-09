module

public import Certificates.Kernel.Sporadic.RawGenSchOJ
public meta import Certificates.Kernel.Sporadic.RawGenSchOJ
public import Certificates.Kernel.Sporadic.Fi24K.D2077
public meta import CFSG.Sporadic.FischerOddCore.Fi24R2KCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi24R

meta def kM : Array (Array Nat) := CFSG.Sporadic.FischerOddCore.fi24KStrong

meta def kB : Array Nat := CFSG.Sporadic.FischerOddCore.fi24KBase

end CertificateChecks.KernelSpor.Fi24R

#ks_rawchain_sl2_data CertificateChecks.KernelSpor.Fi24KC 504 9 16 64
  CertificateChecks.KernelSpor.Fi24R.kM CertificateChecks.KernelSpor.Fi24R.kB 2
  CertificateChecks.KernelSpor.Fi24W.kD

#ks_rawchain_sl2_lv CertificateChecks.KernelSpor.Fi24KC 0 0 8
#ks_rawchain_sl2_lv CertificateChecks.KernelSpor.Fi24KC 1 0 8
#ks_rawchain_sl2_lv CertificateChecks.KernelSpor.Fi24KC 2 0 8
#ks_rawchain_sl2_lv CertificateChecks.KernelSpor.Fi24KC 3 0 8
#ks_rawchain_sl2_lv CertificateChecks.KernelSpor.Fi24KC 4 0 8
#ks_rawchain_sl2_lv CertificateChecks.KernelSpor.Fi24KC 5 0 8
#ks_rawchain_sl2_lv CertificateChecks.KernelSpor.Fi24KC 6 0 8

#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.Fi24KC 1 0 20
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.Fi24KC 2 0 7
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.Fi24KC 3 0 2
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.Fi24KC 4 0 1
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.Fi24KC 5 0 1
#ks_rawchain_sl2_sch CertificateChecks.KernelSpor.Fi24KC 6 0 1

#ks_rawchain_sl2_osub CertificateChecks.KernelSpor.Fi24KC
#ks_rawchain_sl2_scho CertificateChecks.KernelSpor.Fi24KC 0 32

#ks_rawchain_sl2_joino CertificateChecks.KernelSpor.Fi24KC

end
