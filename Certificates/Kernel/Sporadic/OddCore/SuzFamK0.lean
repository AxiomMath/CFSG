module

public import Certificates.Kernel.Sporadic.OddCore.SuzFamS

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzFamD

@[expose] noncomputable def fPart0 (s : Nat) : Bool := imgSl 0 (Nat.add 0 s)

end CertificateChecks.KernelSpor.SuzFamD

#kss_each CertificateChecks.KernelSpor.SuzFamD.FP0 CertificateChecks.KernelSpor.SuzFamD.fPart0 14
#kss_each CertificateChecks.KernelSpor.SuzFamD.IP CertificateChecks.KernelSpor.SuzFamD.incSl 2

end
