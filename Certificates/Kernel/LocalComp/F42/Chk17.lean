module

public import Certificates.Data.Kernel.F42Lev.L17
public import Certificates.Data.Kernel.F42Lev.L18
public import Certificates.Data.Kernel.F42Lev.Sq
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42

@[expose] noncomputable def chk17 (c : Nat) : Bool :=
  stepOK (nat_lit 17) L17 R17 (nat_lit 8) L18 Q17 R18 (nat_lit 7) c

theorem q0_17 : Nat.beq (fldW Q17 (nat_lit 17) (nat_lit 0)) (nat_lit 0) = true := by
  quickRfl

theorem qn_17 : Nat.beq (fldW Q17 (nat_lit 17) (nat_lit 16896)) nL18 = true := by
  quickRfl

end CertificateChecks.KernelLC.F42

end
