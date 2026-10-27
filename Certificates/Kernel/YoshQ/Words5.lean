module

public import Certificates.Kernel.YoshQ.DataM
public import Certificates.Data.Kernel.YoshQ.Param
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic

public section

namespace CertificateChecks.KernelYoshQ

open CFSG.KC.YoshQ CFSG.EvenSporadicStandard.M12Std.Yosh CFSG.Sporadic.Th.Native

set_option maxHeartbeats 0

theorem w_sAct : sActOK = true := by decide +kernel
theorem w_wMem : wMemCheck = true := by decide +kernel
theorem w_kWords : (kWords.all fun w => commT (tblW w) (tblW wJ)) = true := by decide +kernel
theorem w_relNQ00 : relNQCheck 0 0 = true := by decide +kernel
theorem w_relNQ01 : relNQCheck 0 1 = true := by decide +kernel
theorem w_relNQ10 : relNQCheck 1 0 = true := by decide +kernel
theorem w_relNQ11 : relNQCheck 1 1 = true := by decide +kernel
theorem w_fix00 : compFixV 0 0 = true := by decide +kernel
theorem w_fix01 : compFixV 0 1 = true := by decide +kernel
theorem w_fix10 : compFixV 1 0 = true := by decide +kernel
theorem w_fix11 : compFixV 1 1 = true := by decide +kernel
theorem w_inner00 : compInnerV 0 0 = true := by decide +kernel
theorem w_inner01 : compInnerV 0 1 = true := by decide +kernel
theorem w_inner10 : compInnerV 1 0 = true := by decide +kernel
theorem w_inner11 : compInnerV 1 1 = true := by decide +kernel
theorem w_sigma0 : sigmaQCheck 0 = true := by decide +kernel
theorem w_sigma1 : sigmaQCheck 1 = true := by decide +kernel

theorem w_cv : cvCheckOn ((Y.RL.map (tabN 14 5)).toArray) = true := by decide +kernel

end CertificateChecks.KernelYoshQ

end
