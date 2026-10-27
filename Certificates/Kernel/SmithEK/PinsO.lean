module

public import Certificates.Data.SMod20UaStab
public import Certificates.Kernel.SmithEK.OData
public import Certificates.Kernel.SmithEK.Pts

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.F4.Native

theorem c21262pl0 : ((List.range 21).all fun k =>
    pts.L.getD ((po.PL.getD 0 []).getD k 0) 0 == normC (uaVec (wB 0) uaAl[k]!)) = true := by
  decide +kernel

theorem c21262co : uaCo.toList = po.CO := by
  decide +kernel

theorem c21262sw : stabWords.toList.map (fun w => w.1 + 1024 * w.2) = po.SW := by
  decide +kernel

end CertificateChecks.KernelSmithEK
