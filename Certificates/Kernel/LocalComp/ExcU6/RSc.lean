module

public import Certificates.Kernel.LocalComp.ExcU6.Slices
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.ExcU6

@[expose] noncomputable def gSc (s : Nat) : Bool := slS (Nat.add 44 s)

end CertificateChecks.KernelLC.ExcU6

#kc_slices CertificateChecks.KernelLC.ExcU6.RSc CertificateChecks.KernelLC.ExcU6.gSc 21

end
