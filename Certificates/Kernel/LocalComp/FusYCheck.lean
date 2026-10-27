module

public import Certificates.Kernel.LocalComp.Q47Check
public import CFSG.Certificates.Kernel.FusYKSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC.FusY

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.Q47K CFSG.KC.FusYK
open CFSG.ComponentClassification.AS81.Q47 CFSG.ComponentClassification.AS81.HeSylow
open CFSG.ComponentClassification.AS81.FusY CertificateChecks.KernelLC CertificateChecks.KernelLC.Q47

theorem kF16 : fusB q47Form 16 5 q47M16 K16 4 fusYWK16 = true := by quickRfl

theorem kF32 : fusB q47Form 32 6 q47M32 K32 1 fusYWK32 = true := by quickRfl

theorem fus16 : FusOK 16 5 q47M16 K16 := by
  have kx := HeSylowQECheck.kPerm16
  simp only [Bool.and_eq_true] at kx
  obtain ⟨⟨⟨⟨-, pQ⟩, pE⟩, pF⟩, -⟩ := kx
  obtain ⟨b1, b2, -, b4, -, b6, -⟩ := bounds16
  exact ⟨by decide, b1, b2, HeSylowQECheck.pin16 HeSylowQECheck.kBindQ16 pQ HeSylQ.ok (by decide),
    HeSylowQECheck.pin16 HeSylowQECheck.kBindE16 pE HeSylE.ok (by decide),
    HeSylowQECheck.pin16 HeSylowQECheck.kBindF16 pF HeSylF.ok (by decide), b4, b6⟩

theorem fus32 : FusOK 32 6 q47M32 K32 := by
  have ky := HeAutCheck.kPermG
  simp only [Bool.and_eq_true] at ky
  obtain ⟨⟨⟨⟨-, pQ⟩, pE⟩, pF⟩, -⟩ := ky
  obtain ⟨b1, b2, -, b4, -, b6, -⟩ := bounds32
  exact ⟨by decide, b1, b2, HeAutCheck.pin HeAutCheck.kBindQ pQ HeAutQ.ok (by decide),
    HeAutCheck.pin HeAutCheck.kBindE pE HeAutE.ok (by decide),
    HeAutCheck.pin HeAutCheck.kBindF pF HeAutF.ok (by decide), b4, b6⟩

theorem fusYCheck_true : fusYCheck = true := by
  rw [fusYCheck_eq]
  exact fusYK_sound fus16 fus32 (by decide) kF16 kF32

end CertificateChecks.KernelLC.FusY

end
