module

public import Certificates.Kernel.Sporadic.OddCore.ON2123
public import CFSG.Certificates.Kernel.Spor.DecSLProved
public import CFSG.Certificates.Kernel.Spor.PermLProved

public section

namespace CertificateChecks.KernelSpor.ON2123

open CFSG.Sporadic.ONOddCore CFSG.KS.DecSL CFSG.KS.PermL CFSG.ONSchreier.Native

theorem permArr120_of_proved {a : Array Nat} (h : permLK 120 a.toList = true) :
    permArr120 a = true := by
  obtain ⟨h1, h2⟩ := permLK_sound_proved h
  simp [permArr120, h1, h2]

theorem localFormOK_of_proved {c : LocalCert} (h : localFormK c = true) :
    localFormOK c = true := by
  simp only [localFormK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  simp only [localFormOK, Bool.and_eq_true, List.all_eq_true]
  exact ⟨⟨⟨⟨h1, fun a ha => permArr120_of_proved (h2 a ha)⟩, h3⟩, fun r hr =>
    ⟨⟨(h4 r hr).1.1, fun a ha => permArr120_of_proved ((h4 r hr).1.2 a ha)⟩, (h4 r hr).2⟩⟩, h5⟩

theorem facts2123_proved : localFormOK localCert = true := by
  have h : localCert = decodeCert (natsSL LocAutT.chars) := by
    rw [localCert, LocAutT.eq, natsOf_ofList_proved digits]
  rw [h]
  exact localFormOK_of_proved formK

end CertificateChecks.KernelSpor.ON2123

end
