module

public import Certificates.Data.Kernel.SmithEKV
public import Certificates.Kernel.SmithEK.MData
public import Certificates.Kernel.SmithEK.WData
public import Certificates.Kernel.SmithEK.TPack
public import CFSG.Certificates.Kernel.Common.EachTrue

#kc_each CertificateChecks.KernelSmithEK c21260fix_
  (fun c => CFSG.SmithE.K.fixChunkK CertificateChecks.KernelSmithEK.tp.C
    CertificateChecks.KernelSmithEK.wd.W CertificateChecks.KernelSmithEK.pb.P
    CertificateChecks.KernelSmithEK.pts.L (27 * c) 27) 17 33
