module

public import Certificates.Data.Kernel.F42Lev.L20
public import Certificates.Data.Kernel.F42Lev.L21
public import Certificates.Data.Kernel.F42Lev.Sq
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42

@[expose] noncomputable def chk20 (c : Nat) : Bool :=
  stepOK (nat_lit 20) L20 R20 (nat_lit 5) L21 Q20 R21 (nat_lit 4) c

theorem q0_20 : Nat.beq (fldW Q20 (nat_lit 17) (nat_lit 0)) (nat_lit 0) = true := by
  quickRfl

theorem qn_20 : Nat.beq (fldW Q20 (nat_lit 17) (nat_lit 43520)) nL21 = true := by
  quickRfl

end CertificateChecks.KernelLC.F42

end
