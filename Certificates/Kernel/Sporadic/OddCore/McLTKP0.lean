module

public import Certificates.Kernel.Sporadic.OddCore.McLTK
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLTK

@[expose] noncomputable def pS0 (s : Nat) : Bool := pSl s

end CertificateChecks.KernelSpor.McLTK

#kc_slices CertificateChecks.KernelSpor.McLTK.pS0K CertificateChecks.KernelSpor.McLTK.pS0 9

end
