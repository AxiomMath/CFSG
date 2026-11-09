module

public import Certificates.Data.Kernel.F42Lev.L19
public import Certificates.Data.Kernel.F42Lev.L20
public import Certificates.Data.Kernel.F42Lev.Sq
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42

@[expose] noncomputable def chk19 (c : Nat) : Bool :=
  stepOK (nat_lit 19) L19 R19 (nat_lit 6) L20 Q19 R20 (nat_lit 5) c

theorem q0_19 : Nat.beq (fldW Q19 (nat_lit 17) (nat_lit 0)) (nat_lit 0) = true := by
  quickRfl

theorem qn_19 : Nat.beq (fldW Q19 (nat_lit 17) (nat_lit 36352)) nL20 = true := by
  quickRfl

end CertificateChecks.KernelLC.F42

end
