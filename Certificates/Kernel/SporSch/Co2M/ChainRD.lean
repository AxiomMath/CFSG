module

public import Certificates.Kernel.Sporadic.RawGenSplitP
public import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.ChainCheckInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.Sporadic.Co2Schreier

meta def raS : Array (Array Nat) := localRec.chains.rAction.strongArrs

meta def raB : Array Nat := localRec.chains.rAction.baseArr

@[expose] def raD : List (List Int) := localRec.chains.rAction.derivations

end CertificateChecks.KernelSporSch.Co2M

#ks_rawchain_sl2_data CertificateChecks.KernelSporSch.Co2RA 2048 12 32 256
  CertificateChecks.KernelSporSch.Co2M.raS CertificateChecks.KernelSporSch.Co2M.raB 2
  CertificateChecks.KernelSporSch.Co2M.raD

#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2RA 0 0 8
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2RA 1 0 8
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2RA 2 0 8
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2RA 3 0 8
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2RA 4 0 8
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2RA 5 0 8
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2RA 6 0 8
