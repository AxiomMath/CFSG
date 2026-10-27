module

public import Certificates.Kernel.Sporadic.RawGenSplit
public import CFSG.Sporadic.Schreier.RuCheckLInputs
meta import CFSG.Sporadic.Schreier.RuCheckLInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuL

meta def strongM : Array (Array Nat) := CFSG.Sporadic.RuSchreier.ruField4060 5

meta def baseM : Array Nat :=
  CFSG.Sporadic.RuSchreier.ruBaseArr 4060 CFSG.Sporadic.RuSchreier.ruLChainBase

end CertificateChecks.KernelSporSch.RuL

#ks_rawchain_sl2_data CertificateChecks.KernelSporSch.RuLS 4060 12 2 8
  CertificateChecks.KernelSporSch.RuL.strongM CertificateChecks.KernelSporSch.RuL.baseM 3
  CFSG.Sporadic.RuSchreier.ruLChainDerivations

end
