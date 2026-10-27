module

public import Certificates.Data.Kernel.F42Lev.L10
public import Certificates.Data.Kernel.F42Lev.L11
public import Certificates.Kernel.LocalComp.BlockTac
public import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42

@[expose] noncomputable def chk10 (c : Nat) : Bool :=
  stepOK (nat_lit 10) L10 L11 Q10 (nat_lit 0) false c

theorem q0_10 : Nat.beq (fldW Q10 (nat_lit 17) (nat_lit 0)) (nat_lit 0) = true := by quickRfl

theorem qn_10 : Nat.beq (fldW Q10 (nat_lit 17) (nat_lit 576)) nL11 = true := by quickRfl

theorem Lev10 : ∀ t < 576, chk10 t = true := by lc_cover 431

end CertificateChecks.KernelLC.F42

end
