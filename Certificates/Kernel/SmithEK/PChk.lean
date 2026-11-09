module

public import Certificates.Data.Kernel.SmithEKP
public import Certificates.Kernel.SmithEK.Cols
public import CFSG.Certificates.Kernel.SmithEK.RowsSplit
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE.K

theorem pchk_pre : chkPFPre pts.L cs.L = true := by decide +kernel

theorem pchk_len : pts.L.length ≤ 7 * 99 := by decide +kernel

theorem pchk_q : ∀ j < 7, chkPFRows pts.L cs.L (0 + j * 99) 99 = true := by kc_cover 1

theorem pchk_ok : chkPF pts.L cs.L = true := chkPF_of pts.L cs.L 99 7 pchk_pre pchk_len pchk_q

theorem c21106neg_pair : chkPF pts.L (cs.L.set 5 (cs.L.getD 6 [])) = false := by
  decide +kernel

theorem c21106neg_pt : chkPF (pts.L.set 1 (pts.L.getD 2 0)) cs.L = false := by
  decide +kernel

end CertificateChecks.KernelSmithEK
