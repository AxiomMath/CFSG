module

public import Certificates.Kernel.LocalComp.BfsGen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2Data
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2EndData
meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2Data
meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2EndData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.J2End

meta def e0Gens : List (Array Nat) := CFSG.ComponentClassification.RankTwoSporadic.J2.j2E0.toList

meta def nGens : List (Array Nat) :=
  CFSG.ComponentClassification.RankTwoSporadic.J2.j2EndN0.toList

end CertificateChecks.KernelLC.J2End

#lc_bfs CertificateChecks.KernelLC.J2End.E0 CertificateChecks.KernelLC.J2End.e0Gens 315 9
#lc_bfs CertificateChecks.KernelLC.J2End.N CertificateChecks.KernelLC.J2End.nGens 315 9

end
