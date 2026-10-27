module

public import Certificates.Kernel.TwoHS.F27020
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 100

namespace CFSG.KD.TwoHS

theorem ok27020R : ck27020R = true := by quickRfl

end CFSG.KD.TwoHS

end
