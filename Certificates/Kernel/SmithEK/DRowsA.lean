module

public import Certificates.Data.Kernel.SmithEKR
public import Certificates.Kernel.SmithEK.MData
public import Certificates.Kernel.SmithEK.WData
public import CFSG.Certificates.Kernel.Common.EachTrue

#kc_each CertificateChecks.KernelSmithEK c21261row_
  (fun c => CFSG.SmithE.K.dChunkK CertificateChecks.KernelSmithEK.pb.P
    CertificateChecks.KernelSmithEK.wd.M (27 * c) 27) 0 6
