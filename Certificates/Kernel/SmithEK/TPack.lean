module

public import Certificates.Data.Kernel.SmithEKT
public import Certificates.Kernel.SmithEK.Pts
public import Certificates.Kernel.SmithEK.Tab
public import CFSG.Certificates.Kernel.Common.Eval
meta import Certificates.Kernel.SmithEK.GenTP

#kc_eval CertificateChecks.KernelSmithEK tp CertificateChecks.KernelSmithEK.packStep

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE.K

theorem tp_ok : packOK cT.L pts.L tp.C = true := by
  decide +kernel

theorem tp_len : tp.C.length = 20 := by
  decide +kernel

end CertificateChecks.KernelSmithEK
