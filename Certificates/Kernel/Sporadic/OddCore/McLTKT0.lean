module

public import Certificates.Kernel.Sporadic.OddCore.McLTK
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLTK

@[expose] noncomputable def tS0 (s : Nat) : Bool := tSl s

end CertificateChecks.KernelSpor.McLTK

#kc_slices CertificateChecks.KernelSpor.McLTK.tS0K CertificateChecks.KernelSpor.McLTK.tS0 9

end
