module

public import Certificates.Data.Kernel.SmithEKF
public import CFSG.Certificates.Kernel.Common.Eval
meta import Certificates.Kernel.SmithEK.GenT

#kc_eval CertificateChecks.KernelSmithEK cT CertificateChecks.KernelSmithEK.tabStep

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE.K

theorem cT_eq : cT.L = cTabQ := by
  decide +kernel

end CertificateChecks.KernelSmithEK
