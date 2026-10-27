module

public import Certificates.Kernel.McLAS.Rec3A
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLAS

@[expose] noncomputable def c3A3 (i : Nat) : Bool := c3A (Nat.add 117 i)

end CertificateChecks.KernelMcLAS

#kc_slices CertificateChecks.KernelMcLAS.C3A3 CertificateChecks.KernelMcLAS.c3A3 38

end
