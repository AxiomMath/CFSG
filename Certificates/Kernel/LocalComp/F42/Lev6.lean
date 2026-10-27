module

public import Certificates.Data.Kernel.F42Lev.L6
public import Certificates.Data.Kernel.F42Lev.L7
public import Certificates.Kernel.LocalComp.BlockTac
public import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42

@[expose] noncomputable def chk6 (c : Nat) : Bool :=
  stepOK (nat_lit 6) L6 L7 Q6 (nat_lit 0) false c

theorem q0_6 : Nat.beq (fldW Q6 (nat_lit 17) (nat_lit 0)) (nat_lit 0) = true := by quickRfl

theorem qn_6 : Nat.beq (fldW Q6 (nat_lit 17) (nat_lit 80)) nL7 = true := by quickRfl

theorem Lev6 : ∀ t < 80, chk6 t = true := by lc_cover 80

end CertificateChecks.KernelLC.F42

end
