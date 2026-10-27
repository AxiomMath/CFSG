module

public import Certificates.Kernel.Sporadic.OddCore.McLTK
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLTK

@[expose] noncomputable def tS1 (s : Nat) : Bool := tSl (Nat.add 9 s)

end CertificateChecks.KernelSpor.McLTK

#kc_slices CertificateChecks.KernelSpor.McLTK.tS1K CertificateChecks.KernelSpor.McLTK.tS1 9

end
