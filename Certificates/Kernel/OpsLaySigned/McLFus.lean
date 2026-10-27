module

public import Certificates.Kernel.FusLay.McL
public import Certificates.Data.Kernel.OpsLayGKF
public import CFSG.GH74.Generic.GKFMcLInputs
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelOpsLaySigned.McL

open CFSG.KC.OpsLayGKF CFSG.GH74.Generic
open CertificateChecks.KernelFusLay.McL

theorem fus5105_seedA : mclFus.seedA = String.ofList LA := LA_eq

theorem fus5105_seedB : mclFus.seedB = String.ofList LB := LB_eq

theorem fus5105_K : gkfFusK lay A B mclFus = true := by decide +kernel

theorem fus5105_neg : (!gkfFusK lay B A mclFus) = true := by decide +kernel

end CertificateChecks.KernelOpsLaySigned.McL

end
