module

public import Certificates.Data.Kernel.L34QEightK
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.L34QEightK

open CFSG.Certificates.Kernel.PkEnum CFSG.GH74.KGroups.L34

theorem qClosedV642001 : qClosedV = true := by
  decide +kernel

theorem len642001 : ((transL QP21).headD []).length = 21 := by
  decide +kernel

#kc_each CFSG.Certificates.Kernel.L34QEightK.ch642001b 0 7

theorem neg642001 :
    (forceLL (transL QP21) fun T =>
      (blockW T 1).all fun w => testN [] (prodN w) (prodN (invW w))) = false ∧
    (forceLL (transL QP21) fun T => ((blockW T 1).filter fun w =>
      forceD (prodN w) fun x _ => !(x == oneN) &&
        ((List.range 21).all (fun i => p5N x i == i) ||
          (List.range 21).all fun i => p7N x i == i)).length) = 672 := by
  constructor <;> decide +kernel

end CFSG.Certificates.Kernel.L34QEightK
