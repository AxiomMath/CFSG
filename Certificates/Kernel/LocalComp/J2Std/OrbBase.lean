module

public import Certificates.Kernel.J2Cover.AutChain
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import CFSG.Certificates.Kernel.J2StdOrbSound
public import CFSG.Certificates.Kernel.J2StdKeySound
public import CFSG.Certificates.Kernel.BfsPinSetSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSp44J2Tests
import CFSG.Certificates.Kernel.Common.Harness

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.J2Std

open CFSG.KC.Enum CFSG.KC.BfsPin CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.J2StdOrb
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Certificates.Native
open CFSG.ComponentClassification.RankTwoClassical.J2Std CertificateChecks.KernelJ2Cover
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (keyPts)

@[expose] noncomputable def Z1P : Nat := pkA 9 j2StdZ1
@[expose] noncomputable def Z2P : Nat := pkA 9 j2StdZ2
@[expose] noncomputable def A1P : Nat := pkA 9 j2StdA1
@[expose] noncomputable def B1P : Nat := pkA 9 j2StdB1
@[expose] noncomputable def A2P : Nat := pkA 9 j2StdA2
@[expose] noncomputable def B2P : Nat := pkA 9 j2StdB2
@[expose] noncomputable def R1P : Nat := pkA 9 j2A4R1
@[expose] noncomputable def R2P : Nat := pkA 9 j2A4R2
@[expose] noncomputable def Z3P : Nat := pkA 9 j2A4Z3

@[expose] noncomputable def cm (p q : Nat) : Nat := pcomp 315 9 (mask 9) p q

@[expose] noncomputable def iv (p : Nat) : Nat := pinvS 315 9 (mask 9) p

@[expose] noncomputable def cmt (p q : Nat) : Nat := cm (cm p q) (cm (iv p) (iv q))

@[expose] noncomputable def H0P : Nat := cmt A1P B1P
@[expose] noncomputable def H1P : Nat := cmt A2P B2P

theorem hZ1 : j2StdZ1 = unpack 315 9 Z1P := eq_unpack_of_bindListK (by quickRfl)
theorem hZ2 : j2StdZ2 = unpack 315 9 Z2P := eq_unpack_of_bindListK (by quickRfl)
theorem hA1 : j2StdA1 = unpack 315 9 A1P := eq_unpack_of_bindListK (by quickRfl)
theorem hB1 : j2StdB1 = unpack 315 9 B1P := eq_unpack_of_bindListK (by quickRfl)
theorem hA2 : j2StdA2 = unpack 315 9 A2P := eq_unpack_of_bindListK (by quickRfl)
theorem hB2 : j2StdB2 = unpack 315 9 B2P := eq_unpack_of_bindListK (by quickRfl)
theorem hR1 : j2A4R1 = unpack 315 9 R1P := eq_unpack_of_bindListK (by quickRfl)
theorem hR2 : j2A4R2 = unpack 315 9 R2P := eq_unpack_of_bindListK (by quickRfl)
theorem hZ3 : j2A4Z3 = unpack 315 9 Z3P := eq_unpack_of_bindListK (by quickRfl)

abbrev PermP (p : Nat) : Prop := permOK 315 9 (mask 9) (315 * 9) p (iv p) = true

abbrev Can (p : Nat) : Prop := canonK 315 9 (mask 9) (315 * 9) p = true

theorem cm_eq {p q : Nat} (hp : Can p) (hq : Can q) :
    compA 315 (unpack 315 9 p) (unpack 315 9 q) = unpack 315 9 (cm p q) := compA_unpack hp hq

theorem iv_eq {p : Nat} (hp : PermP p) : invCand 315 (unpack 315 9 p) = unpack 315 9 (iv p) :=
  invCand_unpack hp

theorem cmt_eq {p q : Nat} (hp : PermP p) (hq : PermP q) (cp : Can p) (cq : Can q)
    (cpi : Can (iv p)) (cqi : Can (iv q)) :
    commutatorA 315 (unpack 315 9 p) (unpack 315 9 q) = unpack 315 9 (cmt p q) := by
  unfold commutatorA
  rw [iv_eq hp, iv_eq hq, cm_eq cp cq, cm_eq cpi cqi,
    cm_eq (p := cm p q) (q := cm (iv p) (iv q)) (canonK_pcomp cp cq) (canonK_pcomp cpi cqi)]
  rfl

theorem hH0 : j2StdH0 = unpack 315 9 H0P := by
  rw [j2StdH0, hA1, hB1]
  exact cmt_eq (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)

theorem hH1 : j2StdH1 = unpack 315 9 H1P := by
  rw [j2StdH1, hA2, hB2]
  exact cmt_eq (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)

theorem vZ1 : validA 315 j2StdZ1 = true := by rw [hZ1]; exact validA_unpack (by quickRfl)
theorem vZ2 : validA 315 j2StdZ2 = true := by rw [hZ2]; exact validA_unpack (by quickRfl)
theorem vH0 : validA 315 j2StdH0 = true := by rw [hH0]; exact validA_unpack (by quickRfl)
theorem vH1 : validA 315 j2StdH1 = true := by rw [hH1]; exact validA_unpack (by quickRfl)
theorem vR1 : validA 315 j2A4R1 = true := by rw [hR1]; exact validA_unpack (by quickRfl)
theorem vR2 : validA 315 j2A4R2 = true := by rw [hR2]; exact validA_unpack (by quickRfl)
theorem vZ3 : validA 315 j2A4Z3 = true := by rw [hZ3]; exact validA_unpack (by quickRfl)

theorem hsz : rcnt (PA.LR 0) = 315 ∧ rcnt (PA.LR 1) = 160 ∧ rcnt (PA.LR 2) = 12 :=
  ⟨Nat.eq_of_beq_eq_true (by quickRfl), Nat.eq_of_beq_eq_true (by quickRfl),
    Nat.eq_of_beq_eq_true (by quickRfl)⟩

noncomputable abbrev K1 (X : Nat) : Nat → Nat := keyW1 PA.LR PA.TR PA.TRI X

noncomputable abbrev K2 (X Y : Nat) : Nat → Nat := keyW2 PA.LR PA.TR PA.TRI X Y

theorem keyEq1 {X : Nat} {x : Array Nat} (hx : x = unpack 315 9 X) (hv : validA 315 x = true)
    {w : Nat} (hw : w < 604800) : keyAt keyPts (conjW w x) = K1 X w :=
  keyW1_eq binds PA.head PA.hl hsz hx hv hw

theorem keyEq2 {X Y : Nat} {x y : Array Nat} (hx : x = unpack 315 9 X)
    (hvx : validA 315 x = true) (hy : y = unpack 315 9 Y) (hvy : validA 315 y = true) {w : Nat}
    (hw : w < 604800) : keyAt keyPts2 (conjW w x ++ conjW w y) = K2 X Y w :=
  keyW2_eq binds PA.head PA.hl hsz hx hvx hy hvy hw

end CertificateChecks.KernelLC.J2Std

end
