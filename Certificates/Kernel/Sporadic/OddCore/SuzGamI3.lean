module

public import Certificates.Kernel.Sporadic.OddCore.SuzGamS

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.OddCore.SGam

@[expose] noncomputable def img1b (s : Nat) : Bool := img1 (Nat.add (nat_lit 179) s)

end CertificateChecks.KernelSpor.OddCore.SGam

#kss_each CertificateChecks.KernelSpor.OddCore.SGam.I3 CertificateChecks.KernelSpor.OddCore.SGam.img1b 179

end
