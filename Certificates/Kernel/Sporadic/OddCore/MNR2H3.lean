module

public import Certificates.Kernel.Sporadic.OddCore.MNSlF
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.MNd

@[expose] noncomputable def r2HF_3 (s : Nat) : Bool := r2HF (Nat.add (nat_lit 81) s)

end CertificateChecks.KernelSpor.MNd

#kc_slices CertificateChecks.KernelSpor.MNd.R2HF3 CertificateChecks.KernelSpor.MNd.r2HF_3 27

end
