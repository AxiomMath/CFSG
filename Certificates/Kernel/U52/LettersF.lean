module

public import Certificates.Kernel.U52.DefsF
public import Certificates.Data.Kernel.Misc.ArrEnum
public meta import Certificates.Kernel.U52.DefsF
public meta import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public meta import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.BorelTits.CompleteFlag
public import Certificates.Kernel.Misc.Perm.HexCmd

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelU52F.LFP CertificateChecks.KernelU52F.u52eLA 9
#kmisc_packarrs CertificateChecks.KernelU52F.LFPI CertificateChecks.KernelU52F.u52eLI 9

public section

namespace CertificateChecks.KernelU52F

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.ArrEnum

theorem lfBind : ∀ i < 5, arrBind (burnsideF48t_u52eLArr ())[i]! 462 9 (LFP i) = true := by
  intro i hi
  interval_cases i <;> quickRfl

theorem lfPerm : allN 5 (fun i => permOK 462 9 (mask 9) (462 * 9) (LFP i) (LFPI i)) = true := by
  quickRfl

theorem lfiPerm : allN 5 (fun i => permOK 462 9 (mask 9) (462 * 9) (LFPI i) (LFP i)) = true := by
  quickRfl

end CertificateChecks.KernelU52F

end
