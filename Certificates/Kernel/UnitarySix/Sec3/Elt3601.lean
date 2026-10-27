module

public import Certificates.Kernel.UnitarySix.Sec3.C3601A
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3

theorem kA4_parts :
    prodLazyK 693 (693 * 10) CA4.LR CA4.TR (a4L (wK wj₀) (wKI wj₀) (wK wj₀sq) (wKI wj₀sq)) 2 0
      [] = true ∧ prodLazyK 693 (693 * 10) CA4.LR CA4.TR a4PairL 2 0 [] = true := by
  have h := kA4
  unfold a4Run at h
  simp only [strictB_eq, Bool.and_eq_true] at h
  exact h

theorem kZ2S_parts :
    prodLazyK 693 (693 * 10) CZ2S.LR CZ2S.TR
      (z2sL (sec3G 16) (pinvS 693 10 (mask 10) (sec3G 16)) (wK wg232) (wKI wg232)) 1 0
      [] = true ∧ prodLazyK 693 (693 * 10) CZ2S.LR CZ2S.TR z2sPairL 1 0 [] = true := by
  have h := kZ2S
  unfold z2sRun at h
  simp only [strictB_eq, Bool.and_eq_true] at h
  exact h

end CertificateChecks.KernelU6.Sec3
