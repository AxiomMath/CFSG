module

public import Certificates.Data.Kernel.SmithEKW
public import Certificates.Kernel.SmithEK.WData
public import CFSG.Certificates.Kernel.Common.EachTrue

#kc_each CertificateChecks.KernelSmithEK c21104row_
  (fun c => CFSG.SmithE.K.chunkK CertificateChecks.KernelSmithEK.wd.W
    CertificateChecks.KernelSmithEK.wd.M (16 * c) 16) 0 28
