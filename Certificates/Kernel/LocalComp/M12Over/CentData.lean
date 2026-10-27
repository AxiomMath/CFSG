module

public import Certificates.Kernel.LocalComp.BfsGen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12EndData
meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12EndData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.M12Over

meta def cGens : List (Array Nat) :=
  CFSG.ComponentClassification.RankTwoSporadic.M12.m12OverCW.toList

end CertificateChecks.KernelLC.M12Over

#lc_bfs CertificateChecks.KernelLC.M12Over.C CertificateChecks.KernelLC.M12Over.cGens 24 5

end
