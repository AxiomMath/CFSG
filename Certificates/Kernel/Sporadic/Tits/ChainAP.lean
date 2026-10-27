module

public import Certificates.Kernel.Sporadic.RawGenOrb
public import Certificates.Kernel.Misc.Tits.Text
public import CFSG.Sporadic.Schreier.TitsCertCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsCertCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Tits2264

meta def baseAM : Array Nat := CFSG.Sporadic.Schreier.Tits.baseArr 1755
  CFSG.Sporadic.Schreier.Tits.titsAmbientBase

meta def basePM : Array Nat := CFSG.Sporadic.Schreier.Tits.baseArr 1755
  CFSG.Sporadic.Schreier.Tits.titsPerfectBase

end CertificateChecks.KernelSpor.Tits2264

#ks_raworb CertificateChecks.KernelSpor.TitsA 1755 11 64 CFSG.Sporadic.Schreier.Tits.titsAmbientArrs
  CertificateChecks.KernelSpor.Tits2264.baseAM 4 CFSG.Sporadic.Schreier.Tits.titsAmbientDerivations

#ks_raworb CertificateChecks.KernelSpor.TitsP 1755 11 64 CFSG.Sporadic.Schreier.Tits.titsPerfectArrs
  CertificateChecks.KernelSpor.Tits2264.basePM 2 CFSG.Sporadic.Schreier.Tits.titsPerfectDerivations

end
