module

public import Certificates.Data.CoreE1Mathieu
import Certificates.Kernel.LocalComp.BfsGen
meta import Certificates.Data.CoreE1Mathieu
public import Certificates.Data.Kernel.BfsPin

namespace CertificateChecks.KernelLC.M12E1Enum

meta def sG : List (Array Nat) :=
  (Certificates.CoreE1Perm.sGens Certificates.CoreE1Perm.m12E1Data).toList

end CertificateChecks.KernelLC.M12E1Enum

public section

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelLC.M12S CertificateChecks.KernelLC.M12E1Enum.sG 12 4

end
