module

public import Certificates.Kernel.UnitarySix.Sec3.C3602
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS.Raw CFSG.Monster.B.Co2
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3

theorem kA1Orb_parts : prodLazyK 693 (693 * 10) CA1.LR CA1.TR a1OrbL 1 0 [] = true ∧
    prodLazyK 693 (693 * 10) CA1.LR CA1.TR singL 1 0 [] = true := by
  have h := kA1Orb
  unfold a1OrbRun at h
  rwa [Bool.and_eq_true] at h

end CertificateChecks.KernelU6.Sec3
