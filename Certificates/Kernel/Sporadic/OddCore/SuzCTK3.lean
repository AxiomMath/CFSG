module

public import Certificates.Kernel.Sporadic.OddCore.SuzCTS

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzCT

@[expose] noncomputable def kPart3 (s : Nat) : Bool := kSl (Nat.add 45 s)

end CertificateChecks.KernelSpor.SuzCT

#kss_each CertificateChecks.KernelSpor.SuzCT.KP3 CertificateChecks.KernelSpor.SuzCT.kPart3 15

end
