module

public import Certificates.Data.Kernel.F42Lev.L11
public import Certificates.Data.Kernel.F42Lev.L12
public import Certificates.Kernel.LocalComp.BlockTac
public import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42

@[expose] noncomputable def chk11 (c : Nat) : Bool :=
  stepOK (nat_lit 11) L11 L12 Q11 (nat_lit 0) false c

theorem q0_11 : Nat.beq (fldW Q11 (nat_lit 17) (nat_lit 0)) (nat_lit 0) = true := by quickRfl

theorem qn_11 : Nat.beq (fldW Q11 (nat_lit 17) (nat_lit 768)) nL12 = true := by quickRfl

theorem Lev11 : ∀ t < 768, chk11 t = true := by lc_cover 531

end CertificateChecks.KernelLC.F42

end
