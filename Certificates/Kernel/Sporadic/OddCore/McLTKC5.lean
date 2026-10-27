module

public import Certificates.Kernel.Sporadic.OddCore.McLTK
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLTK

@[expose] noncomputable def cS5 (s : Nat) : Bool := cSl (Nat.add 55 s)

end CertificateChecks.KernelSpor.McLTK

#kc_slices CertificateChecks.KernelSpor.McLTK.cS5K CertificateChecks.KernelSpor.McLTK.cS5 11

end
