module

public import CFSG.LieType.Multipliers.Sz8BridgeInputs
import CFSG.LieType.Multipliers.Sz8Matrix
import CFSG.LieType.Multipliers.Sz8Field

public section

namespace CertificateChecks.KernelMiscCoset.C10008

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.Sz8

set_option maxRecDepth 100000

theorem row5 : (allF8.all fun d => decide (ofMat (rootMat (allF8[5]'(by decide)) d) =
    wordArr (genWord (allF8[5]'(by decide)) d))) = true := by
  decide +kernel

end CertificateChecks.KernelMiscCoset.C10008

end
