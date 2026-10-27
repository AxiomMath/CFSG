module

public import Certificates.Kernel.Sporadic.RawGenSplit
public import Certificates.Kernel.SporSch.Ru.Lines
public import CFSG.Sporadic.Schreier.RuCheckChainsInputs
meta import CFSG.Sporadic.Schreier.RuCheckChainsInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuCN

meta def strongC : Array (Array Nat) := CFSG.Sporadic.RuSchreier.ruField4060 1

meta def baseC : Array Nat :=
  CFSG.Sporadic.RuSchreier.ruBaseArr 4060 CFSG.Sporadic.RuSchreier.ruCBase

meta def strongN : Array (Array Nat) := CFSG.Sporadic.RuSchreier.ruField4060 2

meta def baseN : Array Nat :=
  CFSG.Sporadic.RuSchreier.ruBaseArr 4060 CFSG.Sporadic.RuSchreier.ruNBase

end CertificateChecks.KernelSporSch.RuCN

#ks_rawchain_sl2_data CertificateChecks.KernelSporSch.RuCS 4060 12 2 64
  CertificateChecks.KernelSporSch.RuCN.strongC CertificateChecks.KernelSporSch.RuCN.baseC 2
  CFSG.Sporadic.RuSchreier.ruCDerivations

#ks_rawchain_sl2_data CertificateChecks.KernelSporSch.RuNS 4060 12 2 64
  CertificateChecks.KernelSporSch.RuCN.strongN CertificateChecks.KernelSporSch.RuCN.baseN 2
  CFSG.Sporadic.RuSchreier.ruNDerivations

end
