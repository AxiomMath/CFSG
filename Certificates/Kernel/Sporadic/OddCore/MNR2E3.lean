module

public import Certificates.Kernel.Sporadic.OddCore.MNSl
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.MNd

@[expose] noncomputable def r2E_3 (s : Nat) : Bool := r2E (Nat.add (nat_lit 90) s)

end CertificateChecks.KernelSpor.MNd

#kc_slices CertificateChecks.KernelSpor.MNd.R2E3 CertificateChecks.KernelSpor.MNd.r2E_3 30

end
