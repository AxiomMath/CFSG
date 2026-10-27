module

public import Certificates.Kernel.UnitarySix.Sec3.R3601
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3

@[expose] noncomputable def kPF (k : Nat) : Bool := p2Run (4 * k) 4

#kc_each_unfold kPF 0 2 as CertificateChecks.KernelU6.Sec3.kP
#kc_unfold CertificateChecks.KernelU6.Sec3.kP2_ kPF 2
#kc_each_unfold kPF 3 30 as CertificateChecks.KernelU6.Sec3.kP

theorem kP2 : prodLazyK 693 (693 * 10) CK1.LR CK1.TR p2L 3 0 [] = true := by
  refine p2_all fun s hs => ?_
  interval_cases s
  exacts [kP0, kP1, kP2_, kP3, kP4, kP5, kP6, kP7, kP8, kP9, kP10, kP11, kP12, kP13, kP14, kP15,
    kP16, kP17, kP18, kP19, kP20, kP21, kP22, kP23, kP24, kP25, kP26, kP27, kP28, kP29]

end CertificateChecks.KernelU6.Sec3
