module

public import Certificates.Data.Kernel.SmithEKE
public import Certificates.Kernel.SmithEK.Cols
meta import Certificates.Kernel.SmithEK.GenE

#kc_eval CertificateChecks.KernelSmithEK c8c CertificateChecks.KernelSmithEK.c8ColStep cs.L

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K

theorem c8c_Q : c8Q cs.L = c8c.Q := by
  decide +kernel

theorem c8c_S : rigS.map (fun s => cs.L.getD s []) = c8c.S := by
  decide +kernel

end CertificateChecks.KernelSmithEK
