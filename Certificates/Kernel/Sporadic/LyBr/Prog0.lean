module

public import CFSG.Certificates.Kernel.Orders.Cert
public import Certificates.Kernel.Sporadic.LyBr.Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#kc_repo #kc_json_gz CFSG.KD.BrLy "Certificates/Kernel/Sporadic/LyBr/data/hm.json.gz" 58075
  10662110596787591430 (HM0 : List Nat)

public noncomputable section

namespace CFSG.KD.BrLy

theorem hm0 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE HM0 (nat_lit 7)) (nat_lit 1303) =
    true := by
  quickRfl

end CFSG.KD.BrLy

end
