module

public import Certificates.Kernel.SuzThree13637.HypData
public import Certificates.Data.Kernel.Spor.HypKD
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KD.SuzThree13637

open CFSG.KS.HypK

theorem d_inj : dInjOK 11 F.D [0, 2] = true := by quickRfl

theorem len_ok : lenOK F.Yl F.Yp 17 = true := by quickRfl

end CFSG.KD.SuzThree13637

end
