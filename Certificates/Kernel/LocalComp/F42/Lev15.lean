module

public import Certificates.Data.Kernel.F42Lev.L15
public import Certificates.Data.Kernel.F42Lev.L16
public import Certificates.Kernel.LocalComp.BlockTac
public import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42

@[expose] noncomputable def chk15 (c : Nat) : Bool :=
  stepOK (nat_lit 15) L15 L16 Q15 (nat_lit 0) false c

theorem q0_15 : Nat.beq (fldW Q15 (nat_lit 17) (nat_lit 0)) (nat_lit 0) = true := by quickRfl

theorem qn_15 : Nat.beq (fldW Q15 (nat_lit 17) (nat_lit 6144)) nL16 = true := by quickRfl

theorem Lev15 : ∀ t < 6144, chk15 t = true := by lc_cover 367

end CertificateChecks.KernelLC.F42

end
