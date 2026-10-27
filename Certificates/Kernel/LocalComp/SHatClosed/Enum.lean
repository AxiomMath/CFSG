module

public import Certificates.Kernel.LocalComp.BfsGenSl
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3CensusInputs
meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3CensusInputs

namespace CertificateChecks.KernelLC.SHatClosed

open CFSG.ComponentClassification.AS81.Census

meta def lGens : List (Array Nat) := [f2perm g1M, f2perm g2M]

end CertificateChecks.KernelLC.SHatClosed

public section

set_option maxRecDepth 400000

#lc_bfs_sl CertificateChecks.KernelLC.SHatL CertificateChecks.KernelLC.SHatClosed.lGens 64 7 1260

end
