module

public import Certificates.Data.Kernel.F42Lev.L16
public import Certificates.Data.Kernel.F42Lev.L17
public import Certificates.Kernel.LocalComp.BlockTac
public import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42

@[expose] noncomputable def chk16 (c : Nat) : Bool :=
  stepOK (nat_lit 16) L16 L17 Q16 (nat_lit 0) false c

theorem q0_16 : Nat.beq (fldW Q16 (nat_lit 17) (nat_lit 0)) (nat_lit 0) = true := by quickRfl

theorem qn_16 : Nat.beq (fldW Q16 (nat_lit 17) (nat_lit 9216)) nL17 = true := by quickRfl

theorem Lev16 : ∀ t < 9216, chk16 t = true := by lc_cover 324

end CertificateChecks.KernelLC.F42

end
