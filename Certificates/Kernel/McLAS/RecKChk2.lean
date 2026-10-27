module

public import Certificates.Kernel.McLAS.RecK
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLAS

@[expose] noncomputable def cK2 (i : Nat) : Bool := cK (Nat.add 74 i)

end CertificateChecks.KernelMcLAS

#kc_slices CertificateChecks.KernelMcLAS.CK2 CertificateChecks.KernelMcLAS.cK2 36

end
