module

public import Certificates.Kernel.McLAS.RecK
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLAS

@[expose] noncomputable def cK1 (i : Nat) : Bool := cK (Nat.add 37 i)

end CertificateChecks.KernelMcLAS

#kc_slices CertificateChecks.KernelMcLAS.CK1 CertificateChecks.KernelMcLAS.cK1 37

end
