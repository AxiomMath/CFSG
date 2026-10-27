module

public import Certificates.Kernel.YoshQ.DataM
public import Certificates.Data.Kernel.YoshQ.Param
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic

public section

namespace CertificateChecks.KernelYoshQ

open CFSG.KC.YoshQ CFSG.EvenSporadicStandard.M12Std.Yosh

set_option maxHeartbeats 0

theorem w_relP : relPOK = true := by decide +kernel
theorem w_step0 : stepOK 0 = true := by decide +kernel
theorem w_step1 : stepOK 1 = true := by decide +kernel
theorem w_x0 : xOK 0 = true := by decide +kernel
theorem w_x1 : xOK 1 = true := by decide +kernel
theorem w_z00 : zOK 0 0 = true := by decide +kernel
theorem w_z01 : zOK 0 1 = true := by decide +kernel
theorem w_z10 : zOK 1 0 = true := by decide +kernel
theorem w_z11 : zOK 1 1 = true := by decide +kernel

theorem w_xDet : xDeterminedOn ((Y.RL.map (tabN 14 5)).toArray) = true := by decide +kernel

end CertificateChecks.KernelYoshQ

end
