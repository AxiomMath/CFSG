module

public import Certificates.Kernel.Sporadic.OddCore.J2Cent
public import Certificates.Data.Kernel.Spor.MulH
public import Certificates.Data.FooteLitCF23J2Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J2Fus

open CFSG.KC.Enum CFSG.KS CFSG.KS.MulH CFSG.KS.Prim CertificateChecks.KernelSpor

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 315 9 (mask 9) p q

@[expose] noncomputable def idK : Nat := pidn 315 9

@[expose] noncomputable def wI (ks : List Nat) : Nat := wfoldK 315 9 (mask 9) J2CentI ks idK

@[expose] noncomputable def L1 (l : Nat) : Nat := J2CentT.F (l + 17)

@[expose] noncomputable def L12 (l : Nat) : Nat := J2CentT.F ([0, 0, 0, 0, 0, 22, 32, 0, 0, 35].getD l 0)

@[expose] noncomputable def G1 : Nat := wfoldK 315 9 (mask 9) L1 [3, 2] idK
@[expose] noncomputable def G1I : Nat := wI [19, 20]
@[expose] noncomputable def G2 : Nat := wfoldK 315 9 (mask 9) L1 [2, 4, 2, 4] idK
@[expose] noncomputable def G2I : Nat := wI [21, 19, 21, 19]

@[expose] noncomputable def LD (l : Nat) : Nat := [0, G1, G2].getD l 0

@[expose] noncomputable def D0 : Nat := wfoldK 315 9 (mask 9) LD [1, 2, 2] idK
@[expose] noncomputable def C0 : Nat := wfoldK 315 9 (mask 9) L12 [9, 5, 6, 9] idK
@[expose] noncomputable def C0I : Nat := wI [35, 32, 22, 35]

theorem k_canon : allN 42 (fun k => bAnd(canonK 315 9 (mask 9) (315 * 9) (J2CentT.F k),
    canonK 315 9 (mask 9) (315 * 9) (J2CentI k))) = true := by
  quickRfl

theorem k_inv : bAnd(invEqK 315 9 (mask 9) (315 * 9) G1 G1I, bAnd(invEqK 315 9 (mask 9) (315 * 9) G2 G2I,
    bAnd(invEqK 315 9 (mask 9) (315 * 9) C0 C0I, canonK 315 9 (mask 9) (315 * 9) C0I))) = true := by
  quickRfl

theorem k_d0 : bAnd(Nat.beq (pc D0 D0) idK, bIf(Nat.beq D0 idK, false, true)) = true := by
  quickRfl

theorem fusK : Nat.beq (pc (pc C0I (J2CentT.F 17)) C0) (pc (J2CentT.F 17) D0) = true := by
  quickRfl

end CertificateChecks.KernelSpor.J2Fus

end
