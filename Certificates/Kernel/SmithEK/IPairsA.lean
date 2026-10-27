module

public import Certificates.Data.Kernel.SmithEKI
public import Certificates.Kernel.SmithEK.Bas
public import Certificates.Kernel.SmithEK.Pts
public import Certificates.Kernel.SmithEK.WData
public import CFSG.Certificates.Kernel.Common.EachTrue

#kc_each CertificateChecks.KernelSmithEK c21107pair_
  (fun c => CFSG.SmithE.K.chunkI (CFSG.SmithE.K.wBits CertificateChecks.KernelSmithEK.wd.W ||| 1)
    CertificateChecks.KernelSmithEK.pts.L
    (CertificateChecks.KernelSmithEK.bs.L.map CFSG.SmithE.K.spanM) (87 * c) 87) 0 4

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE.K

theorem c21107neg_pair : pairI (wBits wd.W ||| 1) (pts.L.getD 0 0) (spanM (bs.L.getD 0 []))
    (pts.L.getD 1 0) (spanM (bs.L.getD 0 [])) = false := by
  decide +kernel

end CertificateChecks.KernelSmithEK
