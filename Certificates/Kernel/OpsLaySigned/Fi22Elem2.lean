module

public import Certificates.Kernel.FusLay.Fi22
public import Certificates.Data.Kernel.OpsLayElem2
public import CFSG.HardMathSupport.Solomon.Coordinator.I10_21Fi22Inputs

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelOpsLaySigned.Fi22

open CFSG.KC.OpsLayElem2 CFSG.HardMathSupport.Solomon.Coordinator
open CertificateChecks.KernelFusLay.Fi22

theorem elem13501_K : elem2K lay A B (List.ofFn i1021Fi22Word) (List.range 77) = true := by
  decide +kernel

end CertificateChecks.KernelOpsLaySigned.Fi22

end
