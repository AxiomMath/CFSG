module

public import Certificates.Kernel.LocalComp.BfsGen
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Q47Data
meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Q47Data

namespace CertificateChecks.KernelLC.Q47Enum

open CFSG.ComponentClassification.AS81.Q47

meta def uy1 : List (Array Nat) := q47U1Gens ++ q47YGens

meta def uy2 : List (Array Nat) := q47U2Gens ++ q47YGens

end CertificateChecks.KernelLC.Q47Enum

public section

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelLC.Q47Y CFSG.ComponentClassification.AS81.Q47.q47YGens 64 7
#lc_bfs CertificateChecks.KernelLC.Q47N CFSG.ComponentClassification.AS81.Q47.q47NGens 64 7
#lc_bfs CertificateChecks.KernelLC.Q47UY1 CertificateChecks.KernelLC.Q47Enum.uy1 64 7
#lc_bfs CertificateChecks.KernelLC.Q47UY2 CertificateChecks.KernelLC.Q47Enum.uy2 64 7
#lc_bfs CertificateChecks.KernelLC.Q47NE CFSG.ComponentClassification.AS81.Q47.q47NE32 32 6

end
