module

public import Certificates.Kernel.Sporadic.RawGenSplit
public import CFSG.Sporadic.Schreier.RuCheckChainsInputs
meta import CFSG.Sporadic.Schreier.RuCheckChainsInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuS4M

meta def strongS : Array (Array Nat) := CFSG.Sporadic.RuSchreier.ruField4060 4

meta def baseS : Array Nat :=
  CFSG.Sporadic.RuSchreier.ruBaseArr 4060 CFSG.Sporadic.RuSchreier.ruS4060ChainBase

end CertificateChecks.KernelSporSch.RuS4M

#ks_rawchain_sl2_data CertificateChecks.KernelSporSch.RuS4 4060 12 0 16
  CertificateChecks.KernelSporSch.RuS4M.strongS CertificateChecks.KernelSporSch.RuS4M.baseS 4
  CFSG.Sporadic.RuSchreier.ruS4060ChainDerivations

end
