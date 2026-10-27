module

public import Certificates.Kernel.Sporadic.RawGenSch
public import Certificates.Kernel.Sporadic.Fi24K.D2077
public meta import CFSG.Sporadic.FischerOddCore.Fi24R2KCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi24R

meta def kM : Array (Array Nat) := CFSG.Sporadic.FischerOddCore.fi24KStrong

meta def kB : Array Nat := CFSG.Sporadic.FischerOddCore.fi24KBase

end CertificateChecks.KernelSpor.Fi24R

#ks_rawchain_sl2 CertificateChecks.KernelSpor.Fi24KC 504 9 16 64 0
  CertificateChecks.KernelSpor.Fi24R.kM CertificateChecks.KernelSpor.Fi24R.kB 2
  CertificateChecks.KernelSpor.Fi24W.kD

end
