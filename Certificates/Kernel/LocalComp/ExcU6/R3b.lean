module

public import Certificates.Kernel.LocalComp.ExcU6.Slices
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.ExcU6

@[expose] noncomputable def g3b (s : Nat) : Bool := sl3 (Nat.add 17 s)

end CertificateChecks.KernelLC.ExcU6

#kc_slices CertificateChecks.KernelLC.ExcU6.R3b CertificateChecks.KernelLC.ExcU6.g3b 17

end
