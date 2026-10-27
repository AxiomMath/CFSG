module

public import Certificates.Data.Kernel.M24L2.R3
public import Certificates.Kernel.M24L2.Data
public import CFSG.Certificates.Kernel.Common.Each

public section

namespace CertificateChecks.KernelM24L2

open CFSG.KC.M24L2

theorem ident_ok : identCheckK = true := by decide +kernel

@[expose] noncomputable def centK (k : Nat) : Bool := centE (glES.getD k [])

set_option maxHeartbeats 0 in
#kc_each centK 0 20

end CertificateChecks.KernelM24L2
