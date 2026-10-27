module

public import Certificates.Data.Kernel.SmithEKP
public import Certificates.Kernel.SmithEK.Cols

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE.K

theorem pchk_ok : chkPF pts.L cs.L = true := by
  decide +kernel

theorem c21106neg_pair : chkPF pts.L (cs.L.set 5 (cs.L.getD 6 [])) = false := by
  decide +kernel

theorem c21106neg_pt : chkPF (pts.L.set 1 (pts.L.getD 2 0)) cs.L = false := by
  decide +kernel

end CertificateChecks.KernelSmithEK
