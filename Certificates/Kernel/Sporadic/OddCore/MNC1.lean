module

public import Certificates.Kernel.Sporadic.OddCore.MNSl
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.MNd

@[expose] noncomputable def sel1S_1 (s : Nat) : Bool := sel1S (Nat.add (nat_lit 24) s)

end CertificateChecks.KernelSpor.MNd

#kc_slices CertificateChecks.KernelSpor.MNd.C1 CertificateChecks.KernelSpor.MNd.sel1S_1 24

end
