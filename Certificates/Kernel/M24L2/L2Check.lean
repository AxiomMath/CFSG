module

public import Certificates.Data.Kernel.M24L2.L2
public import Certificates.Kernel.M24L2.Data
public import Certificates.Kernel.M24L2.DataB
public import CFSG.Certificates.Kernel.Common.Each

public section

namespace CertificateChecks.KernelM24L2

open CFSG.KC.M24L2

theorem rel_ok : relCheckK = true := by decide +kernel

theorem tC_ok : tCheckK = true := by decide +kernel

theorem tN_ok : tNormCheckK = true := by decide +kernel

theorem b_ok : bCheckK = true := by decide +kernel

@[expose] noncomputable def faK (k : Nat) : Bool := faE glMask faW (glES.getD k [])

@[expose] noncomputable def fbK (k : Nat) : Bool := fbE glMask fbW (glES.getD k [])

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
#kc_each faK 0 20

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
#kc_each fbK 0 20

end CertificateChecks.KernelM24L2
