module

public import Certificates.Data.Kernel.F42Lev.L21
public import Certificates.Data.Kernel.F42Lev.L22
public import Certificates.Data.Kernel.F42Lev.Sq
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42

@[expose] noncomputable def chk21 (c : Nat) : Bool :=
  stepOK (nat_lit 21) L21 R21 (nat_lit 4) L22 Q21 S (nat_lit 3) c

theorem q0_21 : Nat.beq (fldW Q21 (nat_lit 17) (nat_lit 0)) (nat_lit 0) = true := by
  quickRfl

theorem qn_21 : Nat.beq (fldW Q21 (nat_lit 17) (nat_lit 66048)) nL22 = true := by
  quickRfl

end CertificateChecks.KernelLC.F42

end
