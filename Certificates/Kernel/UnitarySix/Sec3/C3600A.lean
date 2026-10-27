module

public import Certificates.Kernel.UnitarySix.Sec3.R3600
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3

theorem kT2_0 : t2Run 0 4 = true := by quickRfl
theorem kT2_1 : t2Run 4 4 = true := by quickRfl
theorem kT2_2 : t2Run 8 4 = true := by quickRfl
theorem kT2_3 : t2Run 12 4 = true := by quickRfl

theorem kT1_0 : t1Run 0 16 = true := by quickRfl
theorem kT1_1 : t1Run 16 16 = true := by quickRfl

theorem kA1_0 : ka1Run 0 128 = true := by quickRfl
theorem kA1_1 : ka1Run 128 128 = true := by quickRfl
theorem kA1_2 : ka1Run 256 128 = true := by quickRfl
theorem kA1_3 : ka1Run 384 128 = true := by quickRfl

@[expose] noncomputable def kA2F (k : Nat) : Bool := ka2Run (2 * k) 2

#kc_each_unfold kA2F 0 16 as CertificateChecks.KernelU6.Sec3.kA2_

theorem kT2 : prodLazyK 693 (693 * 10) CT2.LR CT2.TR
    (t2L (wK wab) (wKI wab) (wK wba) (wKI wba) (wK waba) (wKI waba)) 2 0 [] = true := by
  refine t2_all fun s hs => ?_
  interval_cases s
  exacts [kT2_0, kT2_1, kT2_2, kT2_3]

theorem kT1 : prodLazyK 693 (693 * 10) CT1.LR CT1.TR (t1L (wK wbcb) (wKI wbcb)) 2 0 [] = true := by
  refine t1_all fun s hs => ?_
  interval_cases s
  exacts [kT1_0, kT1_1]

theorem kKa1 : prodLazyK 693 (693 * 10) CA1.LR CA1.TR ka1L 1 0 [] = true := by
  refine ka1_all fun s hs => ?_
  interval_cases s
  exacts [kA1_0, kA1_1, kA1_2, kA1_3]

theorem kKa2 : prodLazyK 693 (693 * 10) CA2.LR CA2.TR (ka2L (wK wu₂) (wKI wu₂)) 3 0 [] = true := by
  refine ka2_all fun s hs => ?_
  interval_cases s
  exacts [kA2_0, kA2_1, kA2_2, kA2_3, kA2_4, kA2_5, kA2_6, kA2_7, kA2_8, kA2_9, kA2_10, kA2_11,
    kA2_12, kA2_13, kA2_14, kA2_15]

end CertificateChecks.KernelU6.Sec3
