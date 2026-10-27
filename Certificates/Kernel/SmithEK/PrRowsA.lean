module

public import Certificates.Data.Kernel.SmithEKPr
public import Certificates.Kernel.SmithEK.TPack
public import CFSG.Certificates.Kernel.Common.EachTrue

#kc_each CertificateChecks.KernelSmithEK c21115row_
  (fun c => CFSG.SmithE.K.pqChk CertificateChecks.KernelSmithEK.tp.C
    CertificateChecks.KernelSmithEK.pts.L (87 * c) 87) 0 4

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE.K

theorem c21115neg_id : pqChk ((List.range 20).map fun m =>
      tp.C.getD m 0 - fld 1 (tp.C.getD m 0) * 2 ^ 20 + 2 ^ m * 2 ^ 20)
    (pts.L.set 1 (pts.L.getD 0 0)) 1 1 = false := by
  decide +kernel

end CertificateChecks.KernelSmithEK
