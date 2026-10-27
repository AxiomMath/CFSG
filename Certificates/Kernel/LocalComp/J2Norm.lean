module

public import Certificates.Kernel.LocalComp.J2NormData
public import CFSG.Certificates.Kernel.LocalCompUnpack
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivJ2Inputs
import CFSG.Certificates.Kernel.Common.Harness
public import Std.Data.HashMap

public section

namespace CertificateChecks.KernelLC.J2Norm

open CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.ComponentClassification.AS81.Sec2
open CFSG.RankThree.Native CFSG.Monster.B.Co2.Native

theorem kBind : (bindArrK (j2NormD2 0) 315 9 PD20 && bindArrK (j2NormD2 1) 315 9 PD21 &&
    bindArrK (j2NormD2 2) 315 9 PD22 && bindArrK (j2NormD5 0) 315 9 PD50 &&
    bindArrK (j2NormD5 1) 315 9 PD51 && bindArrK (j2NormX 0) 315 9 PX0 &&
    bindArrK (j2NormX 1) 315 9 PX1) = true := by
  quickRfl

theorem kComp : (compEqK 315 9 (mask 9) (315 * 9) PD20 PD22 PT2a &&
    compEqK 315 9 (mask 9) (315 * 9) PT2a PD21 PT2b &&
    compEqK 315 9 (mask 9) (315 * 9) PT2b PD21 PT2 &&
    compEqK 315 9 (mask 9) (315 * 9) PD50 PD51 PT5a &&
    compEqK 315 9 (mask 9) (315 * 9) PT5a PD50 PT5b &&
    compEqK 315 9 (mask 9) (315 * 9) PT5b PD51 PT5c &&
    compEqK 315 9 (mask 9) (315 * 9) PT5c PD51 PT5 &&
    compEqK 315 9 (mask 9) (315 * 9) PT2 PT5 PC &&
    compEqK 315 9 (mask 9) (315 * 9) PC PX0 PCX &&
    compEqK 315 9 (mask 9) (315 * 9) PCX PCI PB &&
    compEqK 315 9 (mask 9) (315 * 9) PX1 PX1 PX11 &&
    compEqK 315 9 (mask 9) (315 * 9) PX1 PX11 PB &&
    compEqK 315 9 (mask 9) (315 * 9) PX0 PX1 PX01 &&
    compEqK 315 9 (mask 9) (315 * 9) PX1 PX0 PX01 &&
    compEqK 315 9 (mask 9) (315 * 9) PC PB PCB &&
    compEqK 315 9 (mask 9) (315 * 9) PCB PCI PCBC &&
    compEqK 315 9 (mask 9) (315 * 9) PX0 PB PX0B &&
    compEqK 315 9 (mask 9) (315 * 9) PCBC PX0B (pidn 315 9)) = true := by
  quickRfl

theorem kInv : (invEqK 315 9 (mask 9) (315 * 9) PD20 ID20 &&
    invEqK 315 9 (mask 9) (315 * 9) PD21 ID21 && invEqK 315 9 (mask 9) (315 * 9) PD22 ID22 &&
    invEqK 315 9 (mask 9) (315 * 9) PD50 ID50 && invEqK 315 9 (mask 9) (315 * 9) PD51 ID51 &&
    invEqK 315 9 (mask 9) (315 * 9) PC PCI && idK 315 9 (mask 9)) = true := by
  quickRfl

theorem validA_of_invEqK {p r : Nat} (h : invEqK 315 9 (mask 9) (315 * 9) p r = true) :
    validA 315 (unpack 315 9 p) = true := by
  obtain ⟨e, hi⟩ := invEqK_sound h
  unfold validA
  rw [e]
  exact hi

theorem eqA_unpack_self (p : Nat) : eqA 315 (unpack 315 9 p) (unpack 315 9 p) = true :=
  eqK_sound (Nat.beq_refl p)

theorem j2NormCheck_eq : j2NormCheck = true := by
  have b := kBind
  simp only [Bool.and_eq_true] at b
  obtain ⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩ := b
  have c := kComp
  simp only [Bool.and_eq_true] at c
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩,
    c14⟩, c15⟩, c16⟩, c17⟩, c18⟩ := c
  have v := kInv
  simp only [Bool.and_eq_true] at v
  obtain ⟨⟨⟨⟨⟨⟨v1, v2⟩, v3⟩, v4⟩, v5⟩, v6⟩, hid⟩ := v
  unfold j2NormCheck j2NormB j2NormC j2NormT2 j2NormT5
  rw [unpack_eq_of_bindArrK b1, unpack_eq_of_bindArrK b2, unpack_eq_of_bindArrK b3,
    unpack_eq_of_bindArrK b4, unpack_eq_of_bindArrK b5, unpack_eq_of_bindArrK b6,
    unpack_eq_of_bindArrK b7]
  rw [compEqK_sound c1, compEqK_sound c2, compEqK_sound c3, compEqK_sound c4, compEqK_sound c5,
    compEqK_sound c6, compEqK_sound c7, compEqK_sound c8, compEqK_sound c9,
    (invEqK_sound v6).1, compEqK_sound c10, compEqK_sound c11, compEqK_sound c12,
    compEqK_sound c13, compEqK_sound c14, compEqK_sound c15, compEqK_sound c16,
    compEqK_sound c17, compEqK_sound c18, ← idK_sound hid]
  rw [validA_of_invEqK v1, validA_of_invEqK v2, validA_of_invEqK v3, validA_of_invEqK v4,
    validA_of_invEqK v5, validA_of_invEqK v6, eqA_unpack_self,
    eqA_unpack_self, eqA_unpack_self]
  rfl

end CertificateChecks.KernelLC.J2Norm

end
