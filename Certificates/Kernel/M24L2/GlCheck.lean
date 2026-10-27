module

public import Certificates.Data.Kernel.M24L2.Gl
public import Certificates.Kernel.M24L2.Data
public import CFSG.Certificates.Kernel.Common.Each

public section

namespace CertificateChecks.KernelM24L2

open CFSG.KC.M24L2

set_option maxHeartbeats 0 in
theorem tree_ok :
    Nat.beq (Nat.shiftRight (treeS glES (Nat.shiftLeft 1 (Nat.add 33825 64))) 64) glMask = true := by
  decide +kernel

theorem glE_length : Nat.beq (glES.map List.length).sum 20159 = true := by decide +kernel

@[expose] noncomputable def invK (k : Nat) : Bool := invChk glMask (Nat.mul 4096 k) 4096

set_option maxHeartbeats 0 in
#kc_each invK 0 16

end CertificateChecks.KernelM24L2
