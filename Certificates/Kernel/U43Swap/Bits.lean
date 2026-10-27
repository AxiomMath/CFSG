module

public import Certificates.Kernel.U43Swap.Data
public import CFSG.Certificates.Kernel.Enum.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Swap

open CFSG.KC.Enum

@[expose] noncomputable def hiOK (R : Nat → Nat) (n b : Nat) : Bool :=
  allN n (fun i => Nat.beq (Nat.shiftRight (R i) b) (nat_lit 0))

theorem kHi : bAnd(hiOK QR 64 88, hiOK KC 128 58) = true := by quickRfl

end CertificateChecks.KernelU43Swap

end
