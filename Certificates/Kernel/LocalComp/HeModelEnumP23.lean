module

public import Certificates.Kernel.LocalComp.BfsGen
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeModelsData
meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeModelsData

public section

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelLC.HeMP23 CFSG.ComponentClassification.AS81.HeTri.heP23Gens 64 7

end
