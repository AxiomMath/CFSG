module

public import Certificates.Data.Kernel.SmithEKT
public import Certificates.Kernel.SmithEK.TPack
public import Certificates.Kernel.SmithEK.WData
public import CFSG.Certificates.Kernel.Common.EachTrue

#kc_each CertificateChecks.KernelSmithEK c21105row_
  (fun c => CFSG.SmithE.K.chunkT CertificateChecks.KernelSmithEK.tp.C
    CertificateChecks.KernelSmithEK.wd.W CertificateChecks.KernelSmithEK.pts.L (64 * c) 64) 0 7
