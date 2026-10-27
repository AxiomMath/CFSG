module

public import Certificates.Kernel.Sporadic.RawGenOrb
public import CFSG.Sporadic.HeldB.CertPChainData
public meta import CFSG.Sporadic.HeldB.CertPChainData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.He2112

meta def baseM : Array Nat := CFSG.Sporadic.HeldB.heBase.toArray

@[expose] def derivs : List (List Int) := CFSG.Sporadic.HeldB.heWords.toList.drop 2

end CertificateChecks.KernelSpor.He2112

#ks_raworb CertificateChecks.KernelSpor.HeC 8330 14 64 CFSG.Sporadic.HeldB.heStrongArrs
  CertificateChecks.KernelSpor.He2112.baseM 2 CertificateChecks.KernelSpor.He2112.derivs

end
