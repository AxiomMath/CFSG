
module

public import Certificates.Kernel.Sporadic.RawGenSplitP
public import CFSG.Sporadic.Co2Schreier.ThirdCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.ThirdCheckInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert

meta def thES : Array (Array Nat) := extendArrs (gArrsOf co2PosTable witRec) eDerivs

meta def thEB : Array Nat := witRec.third.baseIndices.toArray

end CertificateChecks.KernelSporSch.Co2M

#ks_rawchain_sl2_data CertificateChecks.KernelSporSch.Co2E 2300 12 8 256
  CertificateChecks.KernelSporSch.Co2M.thES CertificateChecks.KernelSporSch.Co2M.thEB 15
  CFSG.Sporadic.Co2Schreier.eDerivs

#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2E 0 0 9
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2E 1 0 9
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2E 2 0 9
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2E 3 0 9
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2E 4 0 9
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2E 5 0 9
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2E 6 0 9
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2E 7 0 9
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2E 8 0 9
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2E 9 0 9
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2E 10 0 9
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2E 11 0 9
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2E 12 0 9
