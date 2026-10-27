module

public import Certificates.Kernel.McLAS.RecK
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLAS

@[expose] noncomputable def cK0 (i : Nat) : Bool := cK i

end CertificateChecks.KernelMcLAS

#kc_slices CertificateChecks.KernelMcLAS.CK0 CertificateChecks.KernelMcLAS.cK0 37

end
