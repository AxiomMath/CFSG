module

public import Certificates.Kernel.LocalComp.BfsGen
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaData
meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaData

public section

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelLC.HexaT CFSG.ComponentClassification.AS81.Hexa.hexaTGens 64 7
#lc_bfs CertificateChecks.KernelLC.HexaR CFSG.ComponentClassification.AS81.Hexa.hexaR0Gens 64 7
#lc_bfs CertificateChecks.KernelLC.HexaM CFSG.ComponentClassification.AS81.Hexa.hexaMGens 64 7
#lc_bfs CertificateChecks.KernelLC.HexaC CFSG.ComponentClassification.AS81.Hexa.hexaCGens 64 7
#lc_bfs CertificateChecks.KernelLC.HexaN CFSG.ComponentClassification.AS81.Hexa.hexaN0Gens 64 7

end
