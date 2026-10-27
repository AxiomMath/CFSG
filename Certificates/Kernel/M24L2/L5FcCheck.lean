module

public import Certificates.Data.Kernel.M24L2.L5
public import Certificates.Kernel.M24L2.Data
public import Certificates.Kernel.M24L2.DataC
public import CFSG.Certificates.Kernel.Common.Each

public section

namespace CertificateChecks.KernelM24L2

open CFSG.KC.M24L2 CFSG.CGT.L5R

@[expose] noncomputable def s0K (k : Nat) : Bool := sliceL (s0M glMask s0W) (glES.getD k [])

@[expose] noncomputable def s1K (k : Nat) : Bool := sliceL (s1M glMask s1W) (glES.getD k [])

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
#kc_each s0K 0 20

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
#kc_each s1K 0 20

end CertificateChecks.KernelM24L2
