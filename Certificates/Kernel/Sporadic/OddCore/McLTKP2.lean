module

public import Certificates.Kernel.Sporadic.OddCore.McLTK
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLTK

@[expose] noncomputable def pS2 (s : Nat) : Bool := pSl (Nat.add 18 s)

end CertificateChecks.KernelSpor.McLTK

#kc_slices CertificateChecks.KernelSpor.McLTK.pS2K CertificateChecks.KernelSpor.McLTK.pS2 9

end
