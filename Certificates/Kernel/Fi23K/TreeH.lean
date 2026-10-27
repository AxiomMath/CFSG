module

public import Certificates.Kernel.Fi23K.ChkDefs
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kon_slices CFSG.KD.Fi23K.hdAt 0 7

namespace CFSG.KD.Fi23K

set_option Elab.async false

theorem small_ok : tSmall = true := by quickRfl

end CFSG.KD.Fi23K

end
