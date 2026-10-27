module

public import Certificates.Kernel.SmithEK.OData
public import Certificates.Kernel.SmithEK.Pts

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.F4.Native

theorem c21262gen : po.G.map (fun p => pts.L.getD p 0) =
    pts.L.filter (fun c => weightC c == 2) ++ [85] := by
  decide +kernel

end CertificateChecks.KernelSmithEK
