module

public import Certificates.Data.Kernel.F42Lev.L5
public import Certificates.Data.Kernel.F42Lev.L6
public import Certificates.Kernel.LocalComp.BlockTac
public import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42

@[expose] noncomputable def chk5 (c : Nat) : Bool :=
  stepOK (nat_lit 5) L5 L6 Q5 (nat_lit 0) false c

theorem q0_5 : Nat.beq (fldW Q5 (nat_lit 17) (nat_lit 0)) (nat_lit 0) = true := by quickRfl

theorem qn_5 : Nat.beq (fldW Q5 (nat_lit 17) (nat_lit 48)) nL6 = true := by quickRfl

theorem Lev5 : ∀ t < 48, chk5 t = true := by lc_cover 48

end CertificateChecks.KernelLC.F42

end
