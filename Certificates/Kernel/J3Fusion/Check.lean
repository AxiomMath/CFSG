module

public import Certificates.Data.Kernel.TabMatGrp
public import Certificates.Kernel.W4Model.Check
public import Certificates.Kernel.J3Fusion.Rels
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelJ3Fusion

open CFSG.KC.TabMatGrp CertificateChecks.KernelLC.J3Ops CertificateChecks.KernelW4Model

theorem rels_ok : grpK 80 SA.M SB.M 2 3 (segs.map natW)
    ((relPs (invRels ++ clRels ++ clsRels)).map fun q => (natW q.1, natW q.2)) = true := by
  quickRfl

theorem dist_ok : distK 80 SA.M SB.M 2 3 (segs.map natW) (pathSegs.map natW) = true := by
  quickRfl

theorem data_ok : dataOK = true := by decide +kernel

end CertificateChecks.KernelJ3Fusion

end
