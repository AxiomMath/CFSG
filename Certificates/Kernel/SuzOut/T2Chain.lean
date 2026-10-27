module

public import Certificates.Kernel.SuzOut.T2Data
public import Certificates.Kernel.Sporadic.RawGenOrb
meta import Certificates.Data.SuzOutComp

set_option maxRecDepth 400000
public section

namespace CertificateChecks.KernelSuzOut

@[expose] noncomputable def derivX : List (List Int) := CFSG.KC.SuzOut.wordsK T2XwC.chars

@[expose] noncomputable def derivD : List (List Int) := CFSG.KC.SuzOut.wordsK T2DwC.chars

end CertificateChecks.KernelSuzOut

end

namespace CertificateChecks.KernelSuzOut.T2M

open CFSG.ComponentClassification.SuzOutComp.Native

meta def strongX : Array (Array Nat) := t2XStrong

meta def baseX : Array Nat := #[0, 1, 2, 3]

meta def strongD : Array (Array Nat) := t2DStrong

meta def baseD : Array Nat := #[0, 1, 3]

end CertificateChecks.KernelSuzOut.T2M

#ks_raworb CertificateChecks.KernelSuzOut.T2X 396 9 64 CertificateChecks.KernelSuzOut.T2M.strongX
  CertificateChecks.KernelSuzOut.T2M.baseX 2 CertificateChecks.KernelSuzOut.derivX

#ks_raworb CertificateChecks.KernelSuzOut.T2D 396 9 64 CertificateChecks.KernelSuzOut.T2M.strongD
  CertificateChecks.KernelSuzOut.T2M.baseD 2 CertificateChecks.KernelSuzOut.derivD
