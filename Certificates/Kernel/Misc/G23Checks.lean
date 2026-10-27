module

public import Certificates.Data.Kernel.Misc.G23
public import Certificates.Kernel.Misc.G23Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CFSG.KD.Misc.G23

open CFSG.KC.Misc.G23

theorem check : g23K cA cB Ab Bb Rc Pc six = true := by quickRfl

end CFSG.KD.Misc.G23

end
