module

public import Certificates.Data.Kernel.F42Lev.L3
public import Certificates.Data.Kernel.F42Lev.L4
public import Certificates.Kernel.LocalComp.BlockTac
public import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42

@[expose] noncomputable def chk3 (c : Nat) : Bool :=
  stepOK (nat_lit 3) L3 L4 Q3 (nat_lit 0) false c

theorem q0_3 : Nat.beq (fldW Q3 (nat_lit 17) (nat_lit 0)) (nat_lit 0) = true := by quickRfl

theorem qn_3 : Nat.beq (fldW Q3 (nat_lit 17) (nat_lit 16)) nL4 = true := by quickRfl

theorem Lev3 : ∀ t < 16, chk3 t = true := by lc_cover 16

end CertificateChecks.KernelLC.F42

end
