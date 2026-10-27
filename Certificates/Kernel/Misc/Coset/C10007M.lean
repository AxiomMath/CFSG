module

public import CFSG.LieType.Multipliers.Sz8Inputs
import CFSG.LieType.Multipliers.Sz8Matrix
import CFSG.LieType.Multipliers.Sz8Field
import CFSG.LieType.Multipliers.Sz8BridgeInputs
import CFSG.LieType.Multipliers.CoverWords

public section

namespace CertificateChecks.KernelMiscCoset.C10007

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.Sz8

set_option maxRecDepth 100000

theorem matCheck_wWord : matCheck [wWord 0 ++ [(0, false)], wWord 1 ++ [(1, false)]] = true := by
  decide +kernel

end CertificateChecks.KernelMiscCoset.C10007

end
