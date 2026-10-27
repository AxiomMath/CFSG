module

public import Certificates.Data.Kernel.F42Lev.L9
public import Certificates.Data.Kernel.F42Lev.L10
public import Certificates.Kernel.LocalComp.BlockTac
public import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42

@[expose] noncomputable def chk9 (c : Nat) : Bool :=
  stepOK (nat_lit 9) L9 L10 Q9 (nat_lit 0) false c

theorem q0_9 : Nat.beq (fldW Q9 (nat_lit 17) (nat_lit 0)) (nat_lit 0) = true := by quickRfl

theorem qn_9 : Nat.beq (fldW Q9 (nat_lit 17) (nat_lit 384)) nL10 = true := by quickRfl

theorem Lev9 : ∀ t < 384, chk9 t = true := by lc_cover 384

end CertificateChecks.KernelLC.F42

end
