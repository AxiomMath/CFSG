module

public import Certificates.Data.Kernel.F42Lev.L2
public import Certificates.Data.Kernel.F42Lev.L3
public import Certificates.Kernel.LocalComp.BlockTac
public import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42

@[expose] noncomputable def chk2 (c : Nat) : Bool :=
  stepOK (nat_lit 2) L2 L3 Q2 (nat_lit 0) false c

theorem q0_2 : Nat.beq (fldW Q2 (nat_lit 17) (nat_lit 0)) (nat_lit 0) = true := by quickRfl

theorem qn_2 : Nat.beq (fldW Q2 (nat_lit 17) (nat_lit 8)) nL3 = true := by quickRfl

theorem Lev2 : ∀ t < 8, chk2 t = true := by lc_cover 8

end CertificateChecks.KernelLC.F42

end
