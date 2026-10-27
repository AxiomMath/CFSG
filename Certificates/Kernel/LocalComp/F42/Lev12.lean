module

public import Certificates.Data.Kernel.F42Lev.L12
public import Certificates.Data.Kernel.F42Lev.L13
public import Certificates.Kernel.LocalComp.BlockTac
public import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42

@[expose] noncomputable def chk12 (c : Nat) : Bool :=
  stepOK (nat_lit 12) L12 L13 Q12 (nat_lit 0) false c

theorem q0_12 : Nat.beq (fldW Q12 (nat_lit 17) (nat_lit 0)) (nat_lit 0) = true := by quickRfl

theorem qn_12 : Nat.beq (fldW Q12 (nat_lit 17) (nat_lit 1152)) nL13 = true := by quickRfl

theorem Lev12 : ∀ t < 1152, chk12 t = true := by lc_cover 490

end CertificateChecks.KernelLC.F42

end
