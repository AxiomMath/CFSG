module

public import CFSG.Monster.B.TwoA.Census.MonoData
public import Certificates.Kernel.LocalComp.BfsGen
public meta import CFSG.Monster.B.TwoA.Census.MonoData

public section

namespace CertificateChecks.KernelCo0

meta def gensL : List (Array Nat) := CFSG.Monster.B.TwoA.Census.sylowGenArr

end CertificateChecks.KernelCo0

#lc_bfs CertificateChecks.KernelCo0.S CertificateChecks.KernelCo0.gensL 24 5

end
