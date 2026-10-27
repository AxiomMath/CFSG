module

public import Certificates.Kernel.UnitarySix.Sec3.K3604Chk
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KC.Enum CFSG.EvenSmallLie.UnitarySix.YamadaSec3

@[expose] noncomputable def kETF (k : Nat) : Bool := eTransRun (32 * k) 32

#kc_each_unfold kETF 0 21 as CertificateChecks.KernelU6.Sec3.kET

theorem kET21 : eTransRun 672 21 = true := by quickRfl

end CertificateChecks.KernelU6.Sec3
