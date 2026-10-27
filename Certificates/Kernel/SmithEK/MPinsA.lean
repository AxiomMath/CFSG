module

public import Certificates.Data.Kernel.SmithEKM
public import Certificates.Kernel.SmithEK.MData
public import Certificates.Kernel.SmithEK.Pts
public import Certificates.Kernel.SmithEK.WData
public import CFSG.Certificates.Kernel.Common.EachTrue

#kc_each CertificateChecks.KernelSmithEK c21266pin_
  (fun c => CFSG.SmithE.K.ptChunkK CertificateChecks.KernelSmithEK.wd.M
    CertificateChecks.KernelSmithEK.pb.P CertificateChecks.KernelSmithEK.pts.L (27 * c) 27) 0 17
