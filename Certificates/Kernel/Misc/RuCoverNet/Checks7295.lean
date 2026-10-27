module

public import Certificates.Kernel.Misc.RuCoverNet.Data
import CFSG.Certificates.Kernel.Common.EachTrue

public section

set_option maxRecDepth 100000

namespace CFSG.KD.RuCoverNet

open CFSG.KC.YModel CFSG.KC.Misc.RuCoverNet

#kc_each CFSG.KD.RuCoverNet ch7295l
  (fun g => letOK 14 16240 (F CFSG.KAct.RuRho.A (Nat.add (Nat.mul 2 g) 1)) (U g)) 0 3

#kc_each CFSG.KD.RuCoverNet ch7295w (fun i => wordOK 14 6 3 U GP GL i) 0 17

#kc_each CFSG.KD.RuCoverNet ch7295r (fun v => sweqK 14 6 U (RP v) (RL v) 0 0) 0 6

#kc_each CFSG.KD.RuCoverNet ch7295z (fun _ => sweqK 14 6 U (ZP 0) (ZL 0) (ZP 1) (ZL 1)) 0 1

end CFSG.KD.RuCoverNet

end
