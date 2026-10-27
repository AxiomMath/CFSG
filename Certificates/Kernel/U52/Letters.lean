module

public import Certificates.Kernel.U52.Defs
public import Certificates.Data.Kernel.Misc.ArrEnum
public meta import Certificates.Kernel.U52.Defs
public meta import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public meta import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.BorelTits.CompleteFlag
public import Certificates.Kernel.Misc.Perm.HexCmd

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelU52.LP CFSG.ASVolI.burnsideF48t_u52LArr 9
#kmisc_packarrs CertificateChecks.KernelU52.LPI CertificateChecks.KernelU52.u52LI 9

public section

namespace CertificateChecks.KernelU52

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.ArrEnum

theorem lpBind : ∀ i < 4, arrBind burnsideF48t_u52LArr[i]! 462 9 (LP i) = true := by
  intro i hi
  interval_cases i <;> quickRfl

theorem lpPerm : allN 4 (fun i => permOK 462 9 (mask 9) (462 * 9) (LP i) (LPI i)) = true := by
  quickRfl

theorem lpiPerm : allN 4 (fun i => permOK 462 9 (mask 9) (462 * 9) (LPI i) (LP i)) = true := by
  quickRfl

end CertificateChecks.KernelU52

end
