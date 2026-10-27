module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.DecSLSound
public import CFSG.Certificates.Kernel.Spor.PermLSound
public import CFSG.Sporadic.ONOddCore.LocalAutDataCheckInputs
meta import CFSG.Sporadic.ONOddCore.LocalAutDataCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.LocAutT CFSG.Sporadic.ONOddCore.localAutText

namespace CertificateChecks.KernelSpor.ON2123

open CFSG.Sporadic.ONOddCore CFSG.KS.DecSL CFSG.KS.PermL CFSG.ONSchreier.Native

@[expose] noncomputable def localFormK (c : LocalCert) : Bool :=
  c.quotGens.length == 2 && c.quotGens.all (fun a => permLK 120 a.toList) &&
    c.records.map (fun r => (r.diag, r.field, r.graph)) == tripleList &&
    c.records.all (fun r => r.images.length == 2 && r.images.all (fun a => permLK 120 a.toList) &&
      r.lifts.all liftFormOK) &&
    c.records.map (fun r => r.lifts.length) == [4, 0, 0, 4, 0, 0, 0, 0, 0, 4, 4, 0]

theorem permArr120_of {a : Array Nat} (h : permLK 120 a.toList = true) : permArr120 a = true := by
  obtain ⟨h1, h2⟩ := permLK_sound h
  simp [permArr120, h1, h2]

theorem localFormOK_of {c : LocalCert} (h : localFormK c = true) : localFormOK c = true := by
  simp only [localFormK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  simp only [localFormOK, Bool.and_eq_true, List.all_eq_true]
  exact ⟨⟨⟨⟨h1, fun a ha => permArr120_of (h2 a ha)⟩, h3⟩, fun r hr =>
    ⟨⟨(h4 r hr).1.1, fun a ha => permArr120_of ((h4 r hr).1.2 a ha)⟩, (h4 r hr).2⟩⟩, h5⟩

theorem digits : digitsSLOK LocAutT.chars = true := by
  quickRfl

theorem formK : localFormK (decodeCert (natsSL LocAutT.chars)) = true := by
  quickRfl

theorem facts2123 : localFormOK localCert = true := by
  have h : localCert = decodeCert (natsSL LocAutT.chars) := by
    rw [localCert, LocAutT.eq, natsOf_ofList digits]
  rw [h]
  exact localFormOK_of formK

end CertificateChecks.KernelSpor.ON2123

end
