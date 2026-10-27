module

public import Certificates.Data.Kernel.F42Lev.L14
public import Certificates.Data.Kernel.F42Lev.L15
public import Certificates.Kernel.LocalComp.BlockTac
public import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42

@[expose] noncomputable def chk14 (c : Nat) : Bool :=
  stepOK (nat_lit 14) L14 L15 Q14 (nat_lit 0) false c

theorem q0_14 : Nat.beq (fldW Q14 (nat_lit 17) (nat_lit 0)) (nat_lit 0) = true := by quickRfl

theorem qn_14 : Nat.beq (fldW Q14 (nat_lit 17) (nat_lit 4096)) nL15 = true := by quickRfl

theorem Lev14 : ∀ t < 4096, chk14 t = true := by lc_cover 373

end CertificateChecks.KernelLC.F42

end
