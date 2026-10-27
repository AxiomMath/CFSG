module

public import Certificates.Kernel.Sporadic.RawGenSplitP
public import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.ChainCheckInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.Sporadic.Co2Schreier

meta def lsS : Array (Array Nat) := localRec.chains.S.strongArrs

meta def lsB : Array Nat := localRec.chains.S.baseArr

@[expose] def lsD : List (List Int) := localRec.chains.S.derivations

end CertificateChecks.KernelSporSch.Co2M

#ks_rawchain_sl2_data CertificateChecks.KernelSporSch.Co2LS 2300 12 8 256
  CertificateChecks.KernelSporSch.Co2M.lsS CertificateChecks.KernelSporSch.Co2M.lsB 15
  CertificateChecks.KernelSporSch.Co2M.lsD

#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2LS 0 0 9
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2LS 1 0 9
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2LS 2 0 9
