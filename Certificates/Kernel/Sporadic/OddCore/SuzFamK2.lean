module

public import Certificates.Kernel.Sporadic.OddCore.SuzFamS

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzFamD

@[expose] noncomputable def fPart2 (s : Nat) : Bool := imgSl 1 (Nat.add 0 s)

end CertificateChecks.KernelSpor.SuzFamD

#kss_each CertificateChecks.KernelSpor.SuzFamD.FP2 CertificateChecks.KernelSpor.SuzFamD.fPart2 14

end
