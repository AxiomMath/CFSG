module

public import Certificates.Kernel.SporSch.Ru.Perms
public import CFSG.Certificates.Kernel.SporSch.RuSound
public import CFSG.Certificates.Kernel.SporSch.DerivsSound
public import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSporSch.RuLines

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2.Native CertificateChecks.KernelSporSch

theorem row4060 {L : Nat} (hL : L < 45) : ruArr4060 L = unpack 4060 12 (RuT4060.L L) := by
  rw [ruArr4060, ruBytes4060]
  exact row_of RuT4060.eq RuT4060.all hL

theorem row1920 {L : Nat} (hL : L < 41) : ruArr1920 L = unpack 1920 11 (RuT1920.L L) := by
  rw [ruArr1920, ruBytes1920]
  exact row_of RuT1920.eq RuT1920.all hL

theorem row80 {L : Nat} (hL : L < 8) : ruArr80 L = unpack 80 7 (RuT80.L L) := by
  rw [ruArr80, ruBytes80]
  exact row_of RuT80.eq RuT80.all hL

theorem isInv_of {n w P R : Nat} {a : Array Nat} (ha : a = unpack n w P)
    (h : permOK n w (mask w) (n * w) P R = true) :
    isInvA n a (invCand n a) = true := by
  obtain ⟨h1, h2⟩ := invEqK_sound (r := R) h
  rw [ha, h1]
  exact h2

theorem layout : ruLayoutOK ruBytes4060 4060 45 = true ∧ ruLayoutOK ruBytes1920 1920 41 = true ∧
    ruLayoutOK ruBytes80 80 8 = true := by
  rw [ruBytes4060, ruBytes1920, ruBytes80]
  exact ⟨layout_of RuT4060.eq RuT4060.all, layout_of RuT1920.eq RuT1920.all,
    layout_of RuT80.eq RuT80.all⟩

theorem isInv : (∀ L < 45, isInvA 4060 (ruArr4060 L) (invCand 4060 (ruArr4060 L)) = true) ∧
    (∀ L < 41, isInvA 1920 (ruArr1920 L) (invCand 1920 (ruArr1920 L)) = true) ∧
    (∀ L < 8, isInvA 80 (ruArr80 L) (invCand 80 (ruArr80 L)) = true) :=
  ⟨fun L hL => isInv_of (row4060 hL) (perm4060 L hL),
    fun L hL => isInv_of (row1920 hL) (perm1920 L hL),
    fun L hL => isInv_of (row80 hL) (perm80 L hL)⟩

end CertificateChecks.KernelSporSch.RuLines

end
