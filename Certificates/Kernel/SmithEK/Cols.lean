module

public import Certificates.Data.Kernel.SmithEKS
public import CFSG.Certificates.Kernel.Common.Eval
public import Certificates.Kernel.SmithEK.Pts
public import Certificates.Kernel.SmithEK.Tab
meta import Certificates.Kernel.SmithEK.GenC

#kc_eval CertificateChecks.KernelSmithEK cs CertificateChecks.KernelSmithEK.colStep

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE.K

theorem cs_ok : pts.L.map (tvW cT.L) = cs.L := by
  decide +kernel

end CertificateChecks.KernelSmithEK
