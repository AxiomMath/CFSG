module

public import Certificates.Kernel.LocalComp.BfsGen
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeModelsData
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaData
meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeModelsData
meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaData

namespace CertificateChecks.KernelLC.HeModelEnum

open CFSG.ComponentClassification.AS81.Hexa

meta def p12 : List (Array Nat) := hexaTGens ++ hexaCGens

end CertificateChecks.KernelLC.HeModelEnum

public section

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelLC.HeMP12 CertificateChecks.KernelLC.HeModelEnum.p12 64 7
#lc_bfs CertificateChecks.KernelLC.HeMB0 CFSG.ComponentClassification.AS81.HeTri.heB0Gens 64 7
#lc_bfs CertificateChecks.KernelLC.HeMF0 CFSG.ComponentClassification.AS81.HeTri.heF0Gens 64 7
#lc_bfs CertificateChecks.KernelLC.HeMBC CFSG.ComponentClassification.AS81.HeTri.heBCGens 32 6
#lc_bfs CertificateChecks.KernelLC.HeMP0 CFSG.ComponentClassification.AS81.HeTri.heP12CGens 32 6
#lc_bfs CertificateChecks.KernelLC.HeMP1 CFSG.ComponentClassification.AS81.HeTri.heP13CGens 32 6
#lc_bfs CertificateChecks.KernelLC.HeMU0 CFSG.ComponentClassification.AS81.HeTri.heECGens 32 6
#lc_bfs CertificateChecks.KernelLC.HeMU1 CFSG.ComponentClassification.AS81.HeTri.heFCGens 32 6

end
