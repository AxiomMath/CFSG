module

public import Certificates.Kernel.LocalComp.BfsGen
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowData
meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowData

public section

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelLC.HeSylX CFSG.ComponentClassification.AS81.HeSylow.heSyl16 16 5
#lc_bfs CertificateChecks.KernelLC.HeSylQ CFSG.ComponentClassification.AS81.HeSylow.heSylQ16 16 5
#lc_bfs CertificateChecks.KernelLC.HeSylE CFSG.ComponentClassification.AS81.HeSylow.heSylE16 16 5
#lc_bfs CertificateChecks.KernelLC.HeSylF CFSG.ComponentClassification.AS81.HeSylow.heSylF16 16 5
#lc_bfs CertificateChecks.KernelLC.HeSylU CFSG.ComponentClassification.AS81.HeSylow.heSylEz16 16 5

end
