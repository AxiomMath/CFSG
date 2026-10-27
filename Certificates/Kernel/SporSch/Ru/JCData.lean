module

public import Certificates.Kernel.Sporadic.RawGenSplit
public import CFSG.Sporadic.Schreier.RuCheckChainsInputs
meta import CFSG.Sporadic.Schreier.RuCheckChainsInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuJ

meta def strongJ : Array (Array Nat) := CFSG.Sporadic.RuSchreier.ruField4060 3

meta def baseJ : Array Nat :=
  CFSG.Sporadic.RuSchreier.ruBaseArr 4060 CFSG.Sporadic.RuSchreier.ruJoinBase

end CertificateChecks.KernelSporSch.RuJ

#ks_rawchain_sl2_data CertificateChecks.KernelSporSch.RuJS 4060 12 0 16
  CertificateChecks.KernelSporSch.RuJ.strongJ CertificateChecks.KernelSporSch.RuJ.baseJ 4
  CFSG.Sporadic.RuSchreier.ruJoinDerivations

end
