module

public import Certificates.Kernel.Misc.XiD.TP
public import Certificates.Kernel.Misc.T46Data
public import Certificates.Data.Kernel.Misc.Xi
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 200000

namespace CFSG.KD.Misc.Xi

open CFSG.KC.Misc.Xi CFSG.KD.Misc.T46

theorem tabAll : ∀ k < 21, tabK UP TP (33 * k) 33 = true := by kc_cover 1

end CFSG.KD.Misc.Xi

end
