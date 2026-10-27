module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Data.Kernel.OpsLayGKFT
public import CFSG.GH74.Generic.GKFLyInputs
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CertificateChecks.KernelFusLay.Ly 5 111
  CFSG.Blueprint.NativeSporadic.LySeed1 CFSG.Blueprint.NativeSporadic.LySeed2

public section

namespace CertificateChecks.KernelFusLay.Ly

open CFSG.KC.OpsLayGKF CFSG.GH74.Generic

theorem fus5104_seedA : lyFus.seedA = String.ofList LA := LA_eq

theorem fus5104_seedB : lyFus.seedB = String.ofList LB := LB_eq

theorem fus5104_K : gkfFusKT lay A B lyFus = true := by decide +kernel

theorem fus5104_neg_seeds : (!gkfFusKT lay B A lyFus) = true := by decide +kernel

theorem fus5104_neg_exp : (!gkfFusKT lay A B { lyFus with n1s := 5 :: lyFus.n1s.tail }) = true := by
  decide +kernel

end CertificateChecks.KernelFusLay.Ly

end
