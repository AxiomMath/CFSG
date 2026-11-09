module

public import Certificates.Kernel.TwoHS.HarCKP
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum

theorem ntQ_lo : allN 4 (fun r => ntQ r 0) = true := by
  quickRfl

theorem ntQ4 : ntQ 4 0 = true := by
  quickRfl

theorem rlQ_lo : allN 4 (fun r => rlQ r 0) = true := by
  quickRfl

theorem rlQ40 : rlQ 4 0 = true := by
  quickRfl

theorem rlQ50 : rlQ 5 0 = true := by
  quickRfl

theorem rlQ51 : rlQ 5 1 = true := by
  quickRfl

theorem rlQ60 : rlQ 6 0 = true := by
  quickRfl

theorem rlQ61 : rlQ 6 1 = true := by
  quickRfl

theorem mbQ_ok : mbQ = true := by
  quickRfl

end CFSG.KD.TwoHS

end

#kc_each CFSG.KD.TwoHS.ntQ5 0 2
#kc_each CFSG.KD.TwoHS.ntQ6 0 4
#kc_each CFSG.KD.TwoHS.clPQ 0 2
