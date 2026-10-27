module

public import Certificates.Kernel.Sporadic.RawGenSl
public import Certificates.Data.Kernel.Misc.RuSq
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.SquaresInputs
public meta import CFSG.Sporadic.Schreier.RuDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.RuSq

meta def strongM : Array (Array Nat) := CFSG.Sporadic.RuSchreier.ruField4060 4

meta def baseM : Array Nat := #[1, 0]

end CertificateChecks.KernelMisc.RuSq

#ks_rawchain_sl CertificateChecks.KernelMisc.RuSqS 4060 12 0 64 0
  CertificateChecks.KernelMisc.RuSq.strongM CertificateChecks.KernelMisc.RuSq.baseM 4
  CFSG.Sporadic.RuSchreier.ruS4060ChainDerivations

end
