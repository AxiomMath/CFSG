module

public import Certificates.Kernel.UnitarySix.Sec3.K3607Chk
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.EachUnfoldKeyed

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3

theorem kH3607 : h3607Run = true := by quickRfl

@[expose] noncomputable def kC7F (i : Nat) : Bool := c7Run (i / 4) (i % 4)

@[expose] def kC7K (i : Nat) : Nat := i / 4

#kc_each_unfold_keyed kC7F 0 20 as CertificateChecks.KernelU6.Sec3.kC7_ key kC7K eval

end CertificateChecks.KernelU6.Sec3
