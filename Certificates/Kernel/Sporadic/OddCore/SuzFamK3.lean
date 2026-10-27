module

public import Certificates.Kernel.Sporadic.OddCore.SuzFamS

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzFamD

@[expose] noncomputable def fPart3 (s : Nat) : Bool := imgSl 1 (Nat.add 14 s)

end CertificateChecks.KernelSpor.SuzFamD

#kss_each CertificateChecks.KernelSpor.SuzFamD.FP3 CertificateChecks.KernelSpor.SuzFamD.fPart3 14

end
