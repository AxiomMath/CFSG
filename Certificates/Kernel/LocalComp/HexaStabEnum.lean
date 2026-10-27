module

public import Certificates.Kernel.LocalComp.BfsGen
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaStabData
meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaStabData

public section

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelLC.HexaM2 CFSG.ComponentClassification.AS81.Hexa.hexaM2Gens 64 7

end
