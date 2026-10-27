module

public import Certificates.Data.Kernel.SmithEKI
public import Certificates.Kernel.SmithEK.Bas
public import Certificates.Kernel.SmithEK.Pts
public import Certificates.Kernel.SmithEK.WData
public import CFSG.Certificates.Kernel.Common.EachTrue

#kc_each CertificateChecks.KernelSmithEK c21107pair_
  (fun c => CFSG.SmithE.K.chunkI (CFSG.SmithE.K.wBits CertificateChecks.KernelSmithEK.wd.W ||| 1)
    CertificateChecks.KernelSmithEK.pts.L
    (CertificateChecks.KernelSmithEK.bs.L.map CFSG.SmithE.K.spanM) (87 * c) 87) 4 8
