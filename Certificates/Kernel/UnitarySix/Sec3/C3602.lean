module

public import Certificates.Kernel.UnitarySix.Sec3.E3602Chk
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3

theorem kA2Orb : a2OrbRun = true := by quickRfl

theorem kA1Orb : a1OrbRun = true := by quickRfl

theorem kA3O0 : a3OrbRun 0 32 = true := by quickRfl
theorem kA3O1 : a3OrbRun 32 32 = true := by quickRfl
theorem kA3O2 : a3OrbRun 64 32 = true := by quickRfl
theorem kA3O3 : a3OrbRun 96 32 = true := by quickRfl

theorem kA3Orb : prodLazyK 693 (693 * 10) CA3.LR CA3.TR a3OrbL 2 0 [] = true := by
  refine a3Orb_all fun s hs => ?_
  interval_cases s
  exacts [kA3O0, kA3O1, kA3O2, kA3O3]

end CertificateChecks.KernelU6.Sec3
