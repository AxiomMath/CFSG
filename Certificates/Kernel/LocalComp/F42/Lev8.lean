module

public import Certificates.Data.Kernel.F42Lev.L8
public import Certificates.Data.Kernel.F42Lev.L9
public import Certificates.Kernel.LocalComp.BlockTac
public import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42

@[expose] noncomputable def chk8 (c : Nat) : Bool :=
  stepOK (nat_lit 8) L8 L9 Q8 (nat_lit 0) false c

theorem q0_8 : Nat.beq (fldW Q8 (nat_lit 17) (nat_lit 0)) (nat_lit 0) = true := by quickRfl

theorem qn_8 : Nat.beq (fldW Q8 (nat_lit 17) (nat_lit 192)) nL9 = true := by quickRfl

theorem Lev8 : ∀ t < 192, chk8 t = true := by lc_cover 192

end CertificateChecks.KernelLC.F42

end
