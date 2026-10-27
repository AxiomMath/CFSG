module

public import Certificates.Kernel.Misc.Perm.J2CentData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.J2Cent

@[expose] noncomputable def fC0 (a : Nat) : Bool := fC a

#lc_blocks B0 fC0 80 1

end CertificateChecks.KernelMisc.J2Cent

end
