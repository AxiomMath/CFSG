module

public import Certificates.Data.Kernel.M24L2.FC
public import Certificates.Kernel.M24L2.Data
public import Certificates.Kernel.M24L2.DataB
public import CFSG.Certificates.Kernel.Common.Each

public section

namespace CertificateChecks.KernelM24L2

open CFSG.KC.M24L2

theorem dP1_ok : dPart1K = true := by decide +kernel

set_option maxRecDepth 20000 in
theorem dP3_ok : dPart3K = true := by decide +kernel

@[expose] noncomputable def dK (k : Nat) : Bool := dE (glES.getD k [])

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
#kc_each dK 0 20

set_option maxRecDepth 20000 in
theorem dL_sorted : sortedK dL = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem dL_ok : allL (fun d => validK glMask d && normBK d) dL = true := by decide +kernel

@[expose] noncomputable def dLK (k : Nat) : Bool := dLE dL (glES.getD k [])

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
#kc_each dLK 0 20

theorem th_ok : (List.finRange 3).all (fun i => validK glMask (thC i)) = true := by decide +kernel

set_option maxRecDepth 20000 in
theorem glL_zero : (allL fun E => allL (fun e => !(Nat.beq e.1 0)) E) glES = true := by
  decide +kernel

end CertificateChecks.KernelM24L2
