module

public import Certificates.Kernel.UnitarySix.Sec3.R3600
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3

@[expose] noncomputable def kNF (k : Nat) : Bool := normRun (4 * k) 4

#kc_each_unfold kNF 0 30 as CertificateChecks.KernelU6.Sec3.kN

theorem kNorm : prodLazyK 693 (693 * 10) CK1.LR CK1.TR normL 3 0 [] = true := by
  refine norm_all fun s hs => ?_
  interval_cases s
  exacts [kN0, kN1, kN2, kN3, kN4, kN5, kN6, kN7, kN8, kN9, kN10, kN11, kN12, kN13, kN14, kN15,
    kN16, kN17, kN18, kN19, kN20, kN21, kN22, kN23, kN24, kN25, kN26, kN27, kN28, kN29]

end CertificateChecks.KernelU6.Sec3
