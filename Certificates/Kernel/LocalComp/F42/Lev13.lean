module

public import Certificates.Data.Kernel.F42Lev.L13
public import Certificates.Data.Kernel.F42Lev.L14
public import Certificates.Kernel.LocalComp.BlockTac
public import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42

@[expose] noncomputable def chk13 (c : Nat) : Bool :=
  stepOK (nat_lit 13) L13 L14 Q13 (nat_lit 0) false c

theorem q0_13 : Nat.beq (fldW Q13 (nat_lit 17) (nat_lit 0)) (nat_lit 0) = true := by quickRfl

theorem qn_13 : Nat.beq (fldW Q13 (nat_lit 17) (nat_lit 2048)) nL14 = true := by quickRfl

theorem Lev13 : ∀ t < 2048, chk13 t = true := by lc_cover 423

end CertificateChecks.KernelLC.F42

end
