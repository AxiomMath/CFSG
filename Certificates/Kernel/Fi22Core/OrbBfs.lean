module

public import Certificates.Data.Kernel.F3Bfs
public import Certificates.Data.Kernel.Fi22.Orb

public section

namespace CertificateChecks.KernelFi22C

open CFSG.KC.F3Bfs CFSG.Sporadic.Fi22.Native

theorem orbL_bfs :
    bfsOrderOK (orbEntry 0) (orbEntry 1) (orbEntry 2) (orbEntry 3) 3510 = true := by
  decide +kernel

end CertificateChecks.KernelFi22C
