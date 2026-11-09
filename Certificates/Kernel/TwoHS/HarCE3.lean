module

public import Certificates.Kernel.TwoHS.HarCKP
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum

theorem ntE_lo : allN 4 (fun r => ntE r 0) = true := by
  quickRfl

theorem ntE4 : ntE 4 0 = true := by
  quickRfl

end CFSG.KD.TwoHS

end

#kc_each CFSG.KD.TwoHS.ntE5 0 2
#kc_each CFSG.KD.TwoHS.ntE6 0 4
#kc_each CFSG.KD.TwoHS.ntE7 0 8
#kc_each CFSG.KD.TwoHS.ntE8 0 16
