module

public import Certificates.Data.Kernel.F42Lev.L18
public import Certificates.Data.Kernel.F42Lev.L19
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42

@[expose] noncomputable def chk18 (c : Nat) : Bool :=
  stepOK (nat_lit 18) L18 L19 Q18 (nat_lit 0) false c

theorem q0_18 : Nat.beq (fldW Q18 (nat_lit 17) (nat_lit 0)) (nat_lit 0) = true := by
  quickRfl

theorem qn_18 : Nat.beq (fldW Q18 (nat_lit 17) (nat_lit 22016)) nL19 = true := by
  quickRfl

end CertificateChecks.KernelLC.F42

end
