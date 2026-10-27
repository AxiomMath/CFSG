module

public import Certificates.Kernel.UnitarySix.Sec3.R3600
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3

@[expose] noncomputable def kS0F (k : Nat) : Bool := sIntRun0 (4 * k) 4

#kc_each_unfold kS0F 0 8 as CertificateChecks.KernelU6.Sec3.kS0_

theorem kS1 : sIntRun 1 15 = true := by quickRfl

@[expose] noncomputable def kS2F (k : Nat) : Bool := sIntRun (16 + 16 * k) 16

#kc_each_unfold kS2F 0 31 as CertificateChecks.KernelU6.Sec3.kS2_

theorem kSInt : prodLazyK 693 (693 * 10) CS.LR CS.TR
    (sIntL (wK wu₂) (wKI wu₂) (wK wu₁) (wKI wu₁) (wK ww₀) (wKI ww₀)) 3 0 [] = true := by
  refine sInt_all (fun s hs => ?_) kS1 (fun s hs => ?_)
  · interval_cases s
    exacts [kS0_0, kS0_1, kS0_2, kS0_3, kS0_4, kS0_5, kS0_6, kS0_7]
  · interval_cases s
    exacts [kS2_0, kS2_1, kS2_2, kS2_3, kS2_4, kS2_5, kS2_6, kS2_7, kS2_8, kS2_9, kS2_10, kS2_11,
      kS2_12, kS2_13, kS2_14, kS2_15, kS2_16, kS2_17, kS2_18, kS2_19, kS2_20, kS2_21, kS2_22,
      kS2_23, kS2_24, kS2_25, kS2_26, kS2_27, kS2_28, kS2_29, kS2_30]

end CertificateChecks.KernelU6.Sec3
