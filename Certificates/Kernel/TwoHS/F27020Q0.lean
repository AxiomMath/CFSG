module

public import Certificates.Kernel.TwoHS.F27020Q
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.TwoHS

theorem ok27020Q_0 : ck27020Q 0 = true := by quickRfl

end CFSG.KD.TwoHS

end
