module

public import Certificates.Data.Kernel.SmithEKG
public import Certificates.Kernel.SmithEK.MData
public import Certificates.Kernel.SmithEK.WData
public import CFSG.Certificates.Kernel.Common.EachTrue

#kc_each CertificateChecks.KernelSmithEK c21260gram_
  (fun c => CFSG.SmithE.K.gramChunkK CertificateChecks.KernelSmithEK.wd.W
    CertificateChecks.KernelSmithEK.pb.P (27 * c) 27) 17 33
