module

public import Certificates.Data.Kernel.SmithEKX
public import Certificates.Kernel.SmithEK.XData
public import CFSG.Certificates.Kernel.Common.EachTrue

#kc_each CertificateChecks.KernelSmithEK c21264row_
  (fun c => CFSG.SmithE.K.ixChunk CertificateChecks.KernelSmithEK.pn.CP
    CertificateChecks.KernelSmithEK.ix.D (16 * c) 16) 28 42

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE.K

theorem c21264rowLast : ixChunk pn.CP ix.D 672 3 = true := by
  decide +kernel

end CertificateChecks.KernelSmithEK
