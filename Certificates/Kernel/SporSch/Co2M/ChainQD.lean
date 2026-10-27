module

public import Certificates.Kernel.Sporadic.RawGenSplitP
public import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.ChainCheckInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.Sporadic.Co2Schreier

meta def qaS : Array (Array Nat) := localRec.chains.qAction.strongArrs

meta def qaB : Array Nat := localRec.chains.qAction.baseArr

@[expose] def qaD : List (List Int) := localRec.chains.qAction.derivations

end CertificateChecks.KernelSporSch.Co2M

#ks_rawchain_sl2_data CertificateChecks.KernelSporSch.Co2QA 512 10 32 128
  CertificateChecks.KernelSporSch.Co2M.qaS CertificateChecks.KernelSporSch.Co2M.qaB 2
  CertificateChecks.KernelSporSch.Co2M.qaD

#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2QA 0 0 4
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2QA 1 0 4
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2QA 2 0 4
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2QA 3 0 4
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2QA 4 0 4
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2QA 5 0 4
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2QA 6 0 4
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2QA 7 0 4
