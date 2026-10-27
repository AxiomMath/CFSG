module

public import Certificates.Kernel.J2Cover.M22LamK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

theorem kFus : (fusN (LTP 0) (LTP 1)).testBit 0 = true := by quickRfl

theorem negFus : (!(fusN (LTP 0) (Nat.xor (LTP 1) 128)).testBit 0) = true := by quickRfl

end CertificateChecks.KernelJ2Cover

end
