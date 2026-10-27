module

public import CFSG.Quasithin.Background.F7TwoInvSporRuInputs
public import Certificates.Kernel.SporSch.Ru.SevenK
import CFSG.Certificates.Kernel.SporSch.RuPowSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuSeven

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CertificateChecks.KernelSporSch.RuG
  CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Quasithin.F7Two

theorem seven_of {p : Nat} (h : sevenK p = true) : ruSevenChk (unpack 4060 12 p) = true := by
  unfold sevenK at h
  obtain ⟨hp, hn⟩ := (bAnd_iff _ _).1 h
  have idA_eq : idA 4060 = unpack 4060 12 (pidn 4060 12) := (idK_sound idOK).symm
  have hpow := powAppRK_sound (k := 0) (P := pidn 4060 12) (p := p) idA_eq hp
  rw [Nat.add_zero] at hpow
  unfold ruSevenChk
  rw [hpow, idA_eq, eqK_sound (Nat.beq_refl _), neK_sound hn]
  rfl

theorem c7418 : CFSG.Quasithin.F7Two.ruInvChk () = true := by
  have i0 : ruInv ruA0A = unpack 4060 12 A0I := (inv_of a0_eq perm0).1
  have i1 : ruInv ruA1A = unpack 4060 12 A1I := (inv_of a1_eq perm1).1
  have hA : ruCommA ruA0A ruA1A (ruInv ruA0A) (ruInv ruA1A) = unpack 4060 12 CA := by
    rw [ruCommA, i0, i1, a0_eq, a1_eq, compEqK_sound a1, compEqK_sound a2, compEqK_sound a3]
  have hB : ruCommA (compA 4060 ruA1A ruA1A) ruA0A (compA 4060 (ruInv ruA1A) (ruInv ruA1A))
      (ruInv ruA0A) = unpack 4060 12 CB := by
    rw [ruCommA, i0, i1, a0_eq, a1_eq, compEqK_sound b1, compEqK_sound b2, compEqK_sound b3,
      compEqK_sound b4, compEqK_sound b5]
  unfold ruInvChk
  rw [hA, hB, seven_of sevenA, seven_of sevenB]
  rfl

end CertificateChecks.KernelSporSch.RuSeven

end
