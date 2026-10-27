module

public import Certificates.Kernel.Sporadic.OddCore.SuzFamS

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzFamD

@[expose] noncomputable def fPart1 (s : Nat) : Bool := imgSl 0 (Nat.add 14 s)

end CertificateChecks.KernelSpor.SuzFamD

#kss_each CertificateChecks.KernelSpor.SuzFamD.FP1 CertificateChecks.KernelSpor.SuzFamD.fPart1 14

end
