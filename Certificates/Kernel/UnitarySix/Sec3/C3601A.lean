module

public import Certificates.Kernel.UnitarySix.Sec3.R3601
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3

theorem kZS0 : zSRun 0 4 = true := by quickRfl
theorem kZS1 : zSRun 4 4 = true := by quickRfl
theorem kZS2 : zSRun 8 4 = true := by quickRfl
theorem kZS3 : zSRun 12 4 = true := by quickRfl
theorem kZS4 : zSRun 16 4 = true := by quickRfl
theorem kZS5 : zSRun 20 4 = true := by quickRfl
theorem kZS6 : zSRun 24 4 = true := by quickRfl
theorem kZS7 : zSRun 28 4 = true := by quickRfl

theorem kZS : prodLazyK 693 (693 * 10) CA2.LR CA2.TR zSL 3 0 [] = true := by
  refine zS_all fun s hs => ?_
  interval_cases s
  exacts [kZS0, kZS1, kZS2, kZS3, kZS4, kZS5, kZS6, kZS7]

theorem kA20 : a2Run 0 8 = true := by quickRfl
theorem kA21 : a2Run 8 8 = true := by quickRfl
theorem kA22 : a2Run 16 8 = true := by quickRfl
theorem kA23 : a2Run 24 8 = true := by quickRfl

theorem kA2 : prodLazyK 693 (693 * 10) CA2.LR CA2.TR a2L 3 0 [] = true := by
  refine a2_all fun s hs => ?_
  interval_cases s
  exacts [kA20, kA21, kA22, kA23]

theorem kZA30 : zA3Run 0 16 = true := by quickRfl
theorem kZA31 : zA3Run 16 16 = true := by quickRfl
theorem kZA32 : zA3Run 32 16 = true := by quickRfl
theorem kZA33 : zA3Run 48 16 = true := by quickRfl
theorem kZA34 : zA3Run 64 16 = true := by quickRfl
theorem kZA35 : zA3Run 80 16 = true := by quickRfl
theorem kZA36 : zA3Run 96 16 = true := by quickRfl
theorem kZA37 : zA3Run 112 16 = true := by quickRfl

theorem kZA3 : prodLazyK 693 (693 * 10) CA3.LR CA3.TR (zA3L (wK we)) 2 0 [] = true := by
  refine zA3_all fun s hs => ?_
  interval_cases s
  exacts [kZA30, kZA31, kZA32, kZA33, kZA34, kZA35, kZA36, kZA37]

theorem kA10 : a1Run 0 64 = true := by quickRfl
theorem kA11 : a1Run 64 64 = true := by quickRfl
theorem kA12 : a1Run 128 64 = true := by quickRfl
theorem kA13 : a1Run 192 64 = true := by quickRfl
theorem kA14 : a1Run 256 64 = true := by quickRfl
theorem kA15 : a1Run 320 64 = true := by quickRfl
theorem kA16 : a1Run 384 64 = true := by quickRfl
theorem kA17 : a1Run 448 64 = true := by quickRfl

theorem kA1 : prodLazyK 693 (693 * 10) CA1.LR CA1.TR (a1L (wK we)) 1 0 [] = true := by
  refine a1_all fun s hs => ?_
  interval_cases s
  exacts [kA10, kA11, kA12, kA13, kA14, kA15, kA16, kA17]

theorem kA4 : a4Run = true := by quickRfl

theorem kZ2S : z2sRun = true := by quickRfl

end CertificateChecks.KernelU6.Sec3
