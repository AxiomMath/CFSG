module

public import Certificates.Data.Kernel.F42Lev.L0
public import Certificates.Data.Kernel.F42Lev.L1
public import Certificates.Kernel.LocalComp.BlockTac
public import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42

@[expose] noncomputable def chk0 (c : Nat) : Bool :=
  stepOK (nat_lit 0) L0 L1 Q0 (nat_lit 0) false c

theorem q0_0 : Nat.beq (fldW Q0 (nat_lit 17) (nat_lit 0)) (nat_lit 0) = true := by quickRfl

theorem qn_0 : Nat.beq (fldW Q0 (nat_lit 17) (nat_lit 2)) nL1 = true := by quickRfl

theorem Lev0 : ∀ t < 2, chk0 t = true := by lc_cover 2

end CertificateChecks.KernelLC.F42

end
