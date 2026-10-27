module

public import Certificates.Kernel.LocalComp.BfsGen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12Data
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12EndData
meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12Data
meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12EndData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.M12End

meta def e0Gens : List (Array Nat) := CFSG.ComponentClassification.RankTwoSporadic.M12.m12E0.toList

meta def lGens : List (Array Nat) := CFSG.ComponentClassification.RankTwoSporadic.M12.m12EndL.toList

end CertificateChecks.KernelLC.M12End

#lc_bfs CertificateChecks.KernelLC.M12End.E0 CertificateChecks.KernelLC.M12End.e0Gens 24 5
#lc_bfs CertificateChecks.KernelLC.M12End.L CertificateChecks.KernelLC.M12End.lGens 24 5

end
