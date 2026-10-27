module

public import Certificates.Kernel.UnitarySix.Sec3.K3920Chk
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3

theorem kL1_0 : l1Run 0 = true := by quickRfl
theorem kL1_1 : l1Run 1 = true := by quickRfl
theorem kL1_2 : l1Run 2 = true := by quickRfl
theorem kL1_3 : l1Run 3 = true := by quickRfl

@[expose] noncomputable def kQF (k : Nat) : Bool := p4Run (4 * k) 4

#kc_each_unfold kQF 0 30 as CertificateChecks.KernelU6.Sec3.kQ

end CertificateChecks.KernelU6.Sec3
