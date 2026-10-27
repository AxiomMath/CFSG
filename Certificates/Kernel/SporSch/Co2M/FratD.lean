
module

public import Certificates.Kernel.Sporadic.RawGenSplitP
public import CFSG.Sporadic.Co2Schreier.SylowCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.SylowCheckInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.Sporadic.Co2Schreier

meta def frS : Array (Array Nat) := fratStrong

meta def frB : Array Nat := fratBase

end CertificateChecks.KernelSporSch.Co2M

#ks_rawchain_sl2_data CertificateChecks.KernelSporSch.Co2LF 2300 12 8 256
  CertificateChecks.KernelSporSch.Co2M.frS CertificateChecks.KernelSporSch.Co2M.frB 12
  CFSG.Sporadic.Co2Schreier.fratDerivs

#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2LF 0 0 9
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2LF 1 0 9
