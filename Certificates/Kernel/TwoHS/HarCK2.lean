module

public import Certificates.Kernel.TwoHS.HarCK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.EvenSporadicStandard.TwoHS

theorem harC_inv : bAnd(allN 6 (fun j => invYK (UK (harCQPairs.getD j ([], true)).1)
    (pinvY (UK (harCQPairs.getD j ([], true)).1))),
    bAnd(invYK G3K (pinvY G3K), invYK G5K (pinvY G5K))) = true := by
  quickRfl

end CFSG.KD.TwoHS

end
