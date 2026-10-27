module

public import Certificates.Kernel.Sporadic.OddCore.MNSl
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.MNd

@[expose] noncomputable def k2E_1 (s : Nat) : Bool := k2E (Nat.add (nat_lit 14) s)

end CertificateChecks.KernelSpor.MNd

#kc_slices CertificateChecks.KernelSpor.MNd.K2E1 CertificateChecks.KernelSpor.MNd.k2E_1 13
#kc_slices CertificateChecks.KernelSpor.MNd.K2H CertificateChecks.KernelSpor.MNd.k2H 4

end
