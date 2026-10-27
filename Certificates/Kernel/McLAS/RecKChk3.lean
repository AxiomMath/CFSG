module

public import Certificates.Kernel.McLAS.RecK
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLAS

@[expose] noncomputable def cK3 (i : Nat) : Bool := cK (Nat.add 110 i)

end CertificateChecks.KernelMcLAS

#kc_slices CertificateChecks.KernelMcLAS.CK3 CertificateChecks.KernelMcLAS.cK3 36

end
