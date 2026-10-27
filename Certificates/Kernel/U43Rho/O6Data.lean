module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentM10Data
import CFSG.Assembly.LowTwoRankDefs

namespace CertificateChecks.KernelU43Rho

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.PairNative
  CFSG.EvenSporadicStandard.M24Std.CU43

meta def o6M : Array (Array Nat) := #[order6W, invCand 820 order6W]

end CertificateChecks.KernelU43Rho

public section

#kmisc_packarrs CertificateChecks.KernelU43Rho.O6 CertificateChecks.KernelU43Rho.o6M 10

end
