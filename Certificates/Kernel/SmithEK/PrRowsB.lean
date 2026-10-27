module

public import Certificates.Data.Kernel.SmithEKPr
public import Certificates.Kernel.SmithEK.TPack
public import CFSG.Certificates.Kernel.Common.EachTrue

#kc_each CertificateChecks.KernelSmithEK c21115row_
  (fun c => CFSG.SmithE.K.pqChk CertificateChecks.KernelSmithEK.tp.C
    CertificateChecks.KernelSmithEK.pts.L (87 * c) 87) 4 8
