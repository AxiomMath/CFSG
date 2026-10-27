module

public import Certificates.Data.Kernel.M24L2.L5
public import Certificates.Kernel.M24L2.Data
public import Certificates.Kernel.M24L2.DataC
public import CFSG.Certificates.Kernel.Common.Each

public section

namespace CertificateChecks.KernelM24L2

open CFSG.KC.M24L2 CFSG.CGT.L5R

theorem bL_ok : bCheckLK = true := by decide +kernel

theorem wL_ok : wCheckLK = true := by decide +kernel

theorem dP1L_ok : dPart1L = true := by decide +kernel

theorem dP3L_ok : dPart3L = true := by decide +kernel

theorem rep_ok : validK glMask rep2Code = true := by decide +kernel

@[expose] noncomputable def dmK (k : Nat) : Bool := sliceL dML (glES.getD k [])

@[expose] noncomputable def faLK (k : Nat) : Bool := sliceL (faLM glMask faW1 faW2) (glES.getD k [])

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
#kc_each dmK 0 20

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
#kc_each faLK 0 20

end CertificateChecks.KernelM24L2
