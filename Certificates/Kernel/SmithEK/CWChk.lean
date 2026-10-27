module

public import Certificates.Data.Kernel.SmithEKCW
public import Certificates.Data.Kernel.SmithEKW
public import Certificates.Kernel.SmithEK.Cols
public import Certificates.Kernel.SmithEK.WData
meta import Certificates.Kernel.SmithEK.GenCW

#kc_eval CertificateChecks.KernelSmithEK cw CertificateChecks.KernelSmithEK.cwStep

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE.K

theorem cw_ok : cwK (wBits wd.W) cw.E cs.L = true := by
  decide +kernel

theorem c21114neg_shift : cwK (wBits wd.W) (cw.E.drop 1 ++ cw.E.take 1) cs.L = false := by
  decide +kernel

theorem c21114neg_empty : cwK 0 cw.E cs.L = false := by
  decide +kernel

end CertificateChecks.KernelSmithEK
