module

public import Certificates.Data.Kernel.F42Lev.L4
public import Certificates.Data.Kernel.F42Lev.L5
public import Certificates.Kernel.LocalComp.BlockTac
public import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42

@[expose] noncomputable def chk4 (c : Nat) : Bool :=
  stepOK (nat_lit 4) L4 L5 Q4 (nat_lit 0) false c

theorem q0_4 : Nat.beq (fldW Q4 (nat_lit 17) (nat_lit 0)) (nat_lit 0) = true := by quickRfl

theorem qn_4 : Nat.beq (fldW Q4 (nat_lit 17) (nat_lit 32)) nL5 = true := by quickRfl

theorem Lev4 : ∀ t < 32, chk4 t = true := by lc_cover 32

end CertificateChecks.KernelLC.F42

end
