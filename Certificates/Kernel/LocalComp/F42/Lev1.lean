module

public import Certificates.Data.Kernel.F42Lev.L1
public import Certificates.Data.Kernel.F42Lev.L2
public import Certificates.Kernel.LocalComp.BlockTac
public import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42

@[expose] noncomputable def chk1 (c : Nat) : Bool :=
  stepOK (nat_lit 1) L1 L2 Q1 (nat_lit 0) false c

theorem q0_1 : Nat.beq (fldW Q1 (nat_lit 17) (nat_lit 0)) (nat_lit 0) = true := by quickRfl

theorem qn_1 : Nat.beq (fldW Q1 (nat_lit 17) (nat_lit 4)) nL2 = true := by quickRfl

theorem Lev1 : ∀ t < 4, chk1 t = true := by lc_cover 4

end CertificateChecks.KernelLC.F42

end
