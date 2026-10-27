module

public import Certificates.Kernel.UnitarySix.Sec3.K3603
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS.Raw CFSG.Monster.B.Co2
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3

theorem kCN0 : coordNRun 0 128 = true := by quickRfl
theorem kCN1 : coordNRun 128 128 = true := by quickRfl
theorem kCN2 : coordNRun 256 128 = true := by quickRfl
theorem kCN3 : coordNRun 384 128 = true := by quickRfl

theorem kCW : coordWRun = true := by quickRfl

theorem kCW_parts : prodLazyK 693 (693 * 10) CA4.LR CA4.TR coordWL 2 0 [] = true ∧
    prodLazyK 693 (693 * 10) CA4.LR CA4.TR
      (fun L => prodLazyK 693 (693 * 10) CA4.LR CA4.TR (coordWPairL L) 2 0 []) 2 0 [] = true := by
  have h := kCW
  unfold coordWRun at h
  rwa [Bool.and_eq_true] at h

end CertificateChecks.KernelU6.Sec3
