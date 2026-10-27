module

public import Certificates.Data.Kernel.L5.HFP
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.L5.HFPAux

public section

set_option maxRecDepth 100000

#kmisc_packarrs CFSG.Certificates.Kernel.L5H.G72E CertificateChecks.KernelL5.g72Src 80

#kmisc_packarrs CFSG.Certificates.Kernel.L5H.G72M CertificateChecks.KernelL5.g72MulSrc 7

namespace CFSG.Certificates.Kernel.L5H

@[expose] noncomputable def g72GN : List Nat := g72N (G72E 0)

@[expose] noncomputable def g72MP : Nat := G72M 0

end CFSG.Certificates.Kernel.L5H

end
