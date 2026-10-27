module

public import Certificates.Data.Kernel.M24L2.L5
public import Certificates.Kernel.M24L2.Data
public import Certificates.Kernel.M24L2.DataC
public import CFSG.Certificates.Kernel.Common.Each

public section

namespace CertificateChecks.KernelM24L2

open CFSG.KC.M24L2 CFSG.CGT.L5R

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem fbL1_ok : fbLK glMask (betaC 0) true cands1 fbW1 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem fbL2_ok : fbLK glMask gamC false cands2 fbW2 = true := by decide +kernel

@[expose] noncomputable def cdAK (k : Nat) : Bool := sliceL (candM (betaC 0) cands1) (glES.getD k [])

@[expose] noncomputable def cdBK (k : Nat) : Bool := sliceL (candM gamC cands2) (glES.getD k [])

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
#kc_each cdAK 0 20

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
#kc_each cdBK 0 20

end CertificateChecks.KernelM24L2
