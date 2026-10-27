module

public import Certificates.Data.Kernel.SmithEKX
public import Certificates.Kernel.SmithEK.XData
public import CFSG.Certificates.Kernel.Common.EachTrue

#kc_each CertificateChecks.KernelSmithEK c21264row_
  (fun c => CFSG.SmithE.K.ixChunk CertificateChecks.KernelSmithEK.pn.CP
    CertificateChecks.KernelSmithEK.ix.D (16 * c) 16) 14 28
