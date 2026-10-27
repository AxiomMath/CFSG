module

public import Certificates.Kernel.Sporadic.OddCore.BTupCmd
meta import CFSG.Sporadic.SuzRecog.SuzL34.Facts
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

namespace CertificateChecks.KernelSpor.SuzBtXD

open CFSG.Sporadic.SuzRecog.SuzL34Cert

meta def x0G : Array (Array Nat) := #[xA, xBs[0]!]

meta def x1G : Array (Array Nat) := #[xA, xBs[1]!]

meta def x2G : Array (Array Nat) := #[xA, xBs[2]!]

meta def x3G : Array (Array Nat) := #[xA, xBs[3]!]

meta def idB : Array Nat := (List.range 16).toArray

end CertificateChecks.KernelSpor.SuzBtXD

public section

set_option maxRecDepth 400000

#kbtup CertificateChecks.KernelSpor.SuzBtX0 16 4 CertificateChecks.KernelSpor.SuzBtXD.x0G
  CertificateChecks.KernelSpor.SuzBtXD.idB
#kbtup CertificateChecks.KernelSpor.SuzBtX1 16 4 CertificateChecks.KernelSpor.SuzBtXD.x1G
  CertificateChecks.KernelSpor.SuzBtXD.idB
#kbtup CertificateChecks.KernelSpor.SuzBtX2 16 4 CertificateChecks.KernelSpor.SuzBtXD.x2G
  CertificateChecks.KernelSpor.SuzBtXD.idB
#kbtup CertificateChecks.KernelSpor.SuzBtX3 16 4 CertificateChecks.KernelSpor.SuzBtXD.x3G
  CertificateChecks.KernelSpor.SuzBtXD.idB

end
