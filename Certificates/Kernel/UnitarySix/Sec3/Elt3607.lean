module

public import Certificates.Kernel.UnitarySix.Sec3.C3607
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3

theorem kH3607_parts :
    prodLazyK 693 (693 * 10) CZ2S.LR CZ2S.TR c11aL 1 0 [] = true ∧
    prodLazyK 693 (693 * 10) CLam.LR CLam.TR c6L 3 0 [] = true ∧
    prodLazyK 693 (693 * 10) CSig.LR CSig.TR (fun L => strictB (prodL 693 10 (mask 10) L) c9K)
      1 0 [] = true ∧
    prodLazyK 693 (693 * 10) CT1.LR CT1.TR (fun L => strictB (prodL 693 10 (mask 10) L) i5K)
      2 0 [] = true ∧
    prodLazyK 693 (693 * 10) CX1.LR CX1.TR (fun L => prodLazyK 693 (693 * 10) CX3.LR CX3.TR
      (fun L' => strictB (prodL 693 10 (mask 10) L) fun X =>
        strictB (prodL 693 10 (mask 10) L') (i8K X)) 1 0 []) 1 0 [] = true ∧
    prodLazyK 693 (693 * 10) CX3.LR CX3.TR (fun L => strictB (prodL 693 10 (mask 10) L) i8bK)
      1 0 [] = true := by
  have h := kH3607
  unfold h3607Run at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end CertificateChecks.KernelU6.Sec3
