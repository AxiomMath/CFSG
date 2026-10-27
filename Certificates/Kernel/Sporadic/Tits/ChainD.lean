module

public import Certificates.Kernel.Sporadic.RawGenSl
public import Certificates.Kernel.Misc.Tits.Text
public import CFSG.Sporadic.Schreier.TitsCertCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsCertCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Tits2264

meta def baseDM : Array Nat := CFSG.Sporadic.Schreier.Tits.baseArr 1755
  CFSG.Sporadic.Schreier.Tits.titsDerivedBase

end CertificateChecks.KernelSpor.Tits2264

#ks_rawchain_sl CertificateChecks.KernelSpor.TitsD 1755 11 0 32 0
  CFSG.Sporadic.Schreier.Tits.titsDerivedArrs CertificateChecks.KernelSpor.Tits2264.baseDM 2
  CFSG.Sporadic.Schreier.Tits.titsDerivedDerivations

end
