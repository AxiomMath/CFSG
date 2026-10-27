module

public import Certificates.Kernel.Sporadic.RawGenSplit
public import Certificates.Kernel.SporSch.Ru.Lines
public import CFSG.Sporadic.Schreier.RuCheckChainsInputs
meta import CFSG.Sporadic.Schreier.RuCheckChainsInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuSM

meta def strongS : Array (Array Nat) := CFSG.Sporadic.RuSchreier.ruField4060 4

meta def baseS : Array Nat :=
  CFSG.Sporadic.RuSchreier.ruBaseArr 4060 CFSG.Sporadic.RuSchreier.ruS4060ChainBase

end CertificateChecks.KernelSporSch.RuSM

#ks_rawchain_sl2_data CertificateChecks.KernelSporSch.RuSS 4060 12 2 64
  CertificateChecks.KernelSporSch.RuSM.strongS CertificateChecks.KernelSporSch.RuSM.baseS 4
  CFSG.Sporadic.RuSchreier.ruS4060ChainDerivations

end
