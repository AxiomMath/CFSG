module

public import Certificates.Data.Kernel.F42Lev.L7
public import Certificates.Data.Kernel.F42Lev.L8
public import Certificates.Kernel.LocalComp.BlockTac
public import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42

@[expose] noncomputable def chk7 (c : Nat) : Bool :=
  stepOK (nat_lit 7) L7 L8 Q7 (nat_lit 0) false c

theorem q0_7 : Nat.beq (fldW Q7 (nat_lit 17) (nat_lit 0)) (nat_lit 0) = true := by quickRfl

theorem qn_7 : Nat.beq (fldW Q7 (nat_lit 17) (nat_lit 128)) nL8 = true := by quickRfl

theorem Lev7 : ∀ t < 128, chk7 t = true := by lc_cover 128

end CertificateChecks.KernelLC.F42

end
