module

public import Certificates.Data.SolMaxH35J2
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import Certificates.Kernel.J2Cover.AutChains
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.BfsPinUnpack
import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2H35

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native
  CFSG.ComponentClassification.J2Cover CFSG.ComponentClassification.SolMax.H35.J2
  CertificateChecks.KernelJ2Cover

abbrev K (p : Nat) : Prop := canonK 315 9 (mask 9) (315 * 9) p = true

theorem k0 : K (C2B.S 0) := by quickRfl

theorem k1 : K (C2B.S 1) := by quickRfl

theorem kI : K (pidn 315 9) := by quickRfl

theorem cK {p q : Nat} (hp : K p) (hq : K q) : K (pcomp 315 9 (mask 9) p q) := canonK_pcomp hp hq

@[expose] noncomputable def pw5 (p : Nat) : Nat :=
  pcomp 315 9 (mask 9) p (pcomp 315 9 (mask 9) p (pcomp 315 9 (mask 9) p
    (pcomp 315 9 (mask 9) p p)))

theorem kP5 {p : Nat} (hp : K p) : K (pw5 p) := by
  rw [pw5.eq_1]
  exact cK hp (cK hp (cK hp (cK hp hp)))

theorem pow5A_unpack {p : Nat} (hp : K p) : pow5A (unpack 315 9 p) = unpack 315 9 (pw5 p) := by
  rw [pow5A.eq_1, compA_unpack hp hp, compA_unpack hp (cK hp hp),
    compA_unpack hp (cK hp (cK hp hp)), compA_unpack hp (cK hp (cK hp (cK hp hp))), pw5.eq_1]

theorem fixedCount_unpack (P : Nat) : fixedCount 315 (unpack 315 9 P) =
    (List.range 315).countP fun i => pg 9 (mask 9) P i == i := by
  rw [fixedCount.eq_1]
  apply List.countP_congr
  intro i hi
  rw [CFSG.KS.Raw.Orb.unpack_get (List.mem_range.1 hi)]

theorem c1_eq : c1 = unpack 315 9 (C2B.S 0) := by
  rw [c1.eq_1]
  exact c2B_binds.2.2.2.2.1 0 (by norm_num)

theorem c2_eq : c2 = unpack 315 9 (C2B.S 1) := by
  rw [c2.eq_1]
  exact c2B_binds.2.2.2.2.1 1 (by norm_num)

@[expose] noncomputable def G : Nat := pcomp 315 9 (mask 9) (C2B.S 0) (C2B.S 0)

@[expose] noncomputable def H : Nat :=
  pcomp 315 9 (mask 9) G (pcomp 315 9 (mask 9) (C2B.S 1) (C2B.S 1))

@[expose] noncomputable def D : Nat := pcomp 315 9 (mask 9) G H

theorem kG : K G := cK k0 k0

theorem kH : K H := cK kG (cK k1 k1)

theorem kD : K D := cK kG kH

theorem g_eq : gArr = unpack 315 9 G := by
  rw [gArr.eq_1, c1_eq, compA_unpack k0 k0, G.eq_1]

theorem h_eq : hArr = unpack 315 9 H := by
  rw [hArr.eq_1, c1_eq, c2_eq, compA_unpack k0 k0, compA_unpack k1 k1,
    compA_unpack (cK k0 k0) (cK k1 k1), H.eq_1, G.eq_1]

theorem d_eq : dArr = unpack 315 9 D := by
  rw [dArr.eq_1, g_eq, h_eq, compA_unpack kG kH, D.eq_1]

@[expose] noncomputable def packedOK : Bool :=
  Nat.beq (pw5 G) (pidn 315 9) && Nat.beq (pw5 H) (pidn 315 9) &&
    Nat.beq (pcomp 315 9 (mask 9) D D) (pidn 315 9) && !(Nat.beq D (pidn 315 9)) &&
    (List.range 315).countP (fun i => pg 9 (mask 9) D i == i) == 11

theorem packedOK_true : packedOK = true := by quickRfl

theorem j2H35Check_true : j2H35Check = true := by
  rw [j2H35Check.eq_1, g_eq, h_eq, d_eq, pow5A_unpack kG, pow5A_unpack kH, compA_unpack kD kD,
    idA_eq (by quickRfl), eqA_unpack (kP5 kG) kI, eqA_unpack (kP5 kH) kI,
    eqA_unpack (cK kD kD) kI, eqA_unpack kD kI, fixedCount_unpack]
  exact packedOK_true

end CertificateChecks.KernelJ2H35

end
