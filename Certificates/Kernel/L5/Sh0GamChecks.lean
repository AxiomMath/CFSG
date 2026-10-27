module

public import Certificates.Data.Kernel.L5.Sh0Gam
import CFSG.Certificates.Kernel.Common.Each

public section

namespace CFSG.Certificates.Kernel.L5S

set_option maxRecDepth 100000

theorem wdChkK_true : wdChkK = true := by decide +kernel

theorem relsChkK_true : relsChkK = true := by decide +kernel

#kc_each CFSG.Certificates.Kernel.L5S.gamK 0 4

theorem gamChkT_neg : (!gamChkT tF iT (gamL 0) (List.range 128) 0) = true := by
  decide +kernel

theorem wdChkK_neg : (!((List.range 128).all fun i =>
    decide (evFromT tF gsK 0 ((wdK.set 1 [1]).getD i []) = i))) = true := by
  decide +kernel

end CFSG.Certificates.Kernel.L5S

end
