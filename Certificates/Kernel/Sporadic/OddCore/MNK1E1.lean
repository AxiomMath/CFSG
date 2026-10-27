module

public import Certificates.Kernel.Sporadic.OddCore.MNSl
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.MNd

@[expose] noncomputable def k1E_1 (s : Nat) : Bool := k1E (Nat.add (nat_lit 24) s)

end CertificateChecks.KernelSpor.MNd

#kc_slices CertificateChecks.KernelSpor.MNd.K1E1 CertificateChecks.KernelSpor.MNd.k1E_1 24

end
