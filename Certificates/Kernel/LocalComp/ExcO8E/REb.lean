module

public import Certificates.Kernel.LocalComp.ExcO8E.Slices
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.ExcO8E

@[expose] noncomputable def gEb (s : Nat) : Bool := slE (Nat.add 37 s)

end CertificateChecks.KernelLC.ExcO8E

#kc_slices CertificateChecks.KernelLC.ExcO8E.REb CertificateChecks.KernelLC.ExcO8E.gEb 36

end
