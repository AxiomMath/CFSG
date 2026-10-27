module

public import Certificates.Kernel.Sporadic.RawGenOrb
public import Certificates.Kernel.SporSch.Ru.Lines
public import CFSG.Sporadic.Schreier.RuCheckChainsInputs
meta import CFSG.Sporadic.Schreier.RuCheckChainsInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuJO'

meta def strongJ : Array (Array Nat) := CFSG.Sporadic.RuSchreier.ruField4060 3

meta def baseJ : Array Nat :=
  CFSG.Sporadic.RuSchreier.ruBaseArr 4060 CFSG.Sporadic.RuSchreier.ruJoinBase

end CertificateChecks.KernelSporSch.RuJO'

#ks_raworb CertificateChecks.KernelSporSch.RuJO 4060 12 16
  CertificateChecks.KernelSporSch.RuJO'.strongJ CertificateChecks.KernelSporSch.RuJO'.baseJ 4
  CFSG.Sporadic.RuSchreier.ruJoinDerivations

end
