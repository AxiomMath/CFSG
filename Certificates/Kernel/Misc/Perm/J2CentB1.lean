module

public import Certificates.Kernel.Misc.Perm.J2CentData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.J2Cent

@[expose] noncomputable def fC1 (a : Nat) : Bool := fC (Nat.add 80 a)

#lc_blocks B1 fC1 80 1

end CertificateChecks.KernelMisc.J2Cent

end
