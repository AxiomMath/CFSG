module

public import Certificates.Kernel.Sporadic.RawGenSplit
public import CFSG.Sporadic.Schreier.RuCheckChainsInputs
meta import CFSG.Sporadic.Schreier.RuCheckChainsInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuSC

open CFSG.Sporadic.RuSchreier

meta def sF : Array (Array Nat) := ruField1920 0
meta def bF : Array Nat := ruBaseArr 1920 ruCFaithfulBase
meta def sS : Array (Array Nat) := ruField1920 1
meta def bS : Array Nat := ruBaseArr 1920 ruSBase

end CertificateChecks.KernelSporSch.RuSC

#ks_rawchain_sl2_data CertificateChecks.KernelSporSch.RuFS 1920 11 2 16
  CertificateChecks.KernelSporSch.RuSC.sF CertificateChecks.KernelSporSch.RuSC.bF 2
  CFSG.Sporadic.RuSchreier.ruCFaithfulDerivations

#ks_rawchain_sl2_data CertificateChecks.KernelSporSch.RuSS2 1920 11 2 16
  CertificateChecks.KernelSporSch.RuSC.sS CertificateChecks.KernelSporSch.RuSC.bS 4
  CFSG.Sporadic.RuSchreier.ruSDerivations

end
