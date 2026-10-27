module

public import Certificates.Kernel.Sporadic.OddCore.SuzCTS

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzCT

@[expose] noncomputable def kPart2 (s : Nat) : Bool := kSl (Nat.add 30 s)

end CertificateChecks.KernelSpor.SuzCT

#kss_each CertificateChecks.KernelSpor.SuzCT.KP2 CertificateChecks.KernelSpor.SuzCT.kPart2 15

end
