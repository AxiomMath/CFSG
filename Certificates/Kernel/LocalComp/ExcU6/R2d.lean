module

public import Certificates.Kernel.LocalComp.ExcU6.Slices
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.ExcU6

@[expose] noncomputable def g2d (s : Nat) : Bool := sl2 (Nat.add 36 s)

end CertificateChecks.KernelLC.ExcU6

#kc_slices CertificateChecks.KernelLC.ExcU6.R2d CertificateChecks.KernelLC.ExcU6.g2d 17

end
