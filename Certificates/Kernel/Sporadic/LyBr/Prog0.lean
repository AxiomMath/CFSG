module

public import CFSG.Certificates.Kernel.Orders.Cert
public import Certificates.Kernel.Sporadic.LyBr.Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#kc_repo #kc_json CFSG.KD.BrLy "Certificates/Kernel/Sporadic/LyBr/data/hm.json" 58075
  10662110596787591430 (HM0 : List Nat)

public noncomputable section

namespace CFSG.KD.BrLy

theorem hm0_0 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM0.drop 0).take 6) (nat_lit 7))
    (nat_lit 151) = true := by
  quickRfl

theorem hm0_1 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM0.drop 6).take 6) (nat_lit 151))
    (nat_lit 295) = true := by
  quickRfl

theorem hm0_2 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM0.drop 12).take 6) (nat_lit 295))
    (nat_lit 439) = true := by
  quickRfl

theorem hm0_3 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM0.drop 18).take 6) (nat_lit 439))
    (nat_lit 583) = true := by
  quickRfl

theorem hm0_4 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM0.drop 24).take 6) (nat_lit 583))
    (nat_lit 727) = true := by
  quickRfl

theorem hm0_5 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM0.drop 30).take 6) (nat_lit 727))
    (nat_lit 871) = true := by
  quickRfl

theorem hm0_6 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM0.drop 36).take 6) (nat_lit 871))
    (nat_lit 1015) = true := by
  quickRfl

theorem hm0_7 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM0.drop 42).take 6) (nat_lit 1015))
    (nat_lit 1159) = true := by
  quickRfl

theorem hm0_8 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM0.drop 48).take 6) (nat_lit 1159))
    (nat_lit 1303) = true := by
  quickRfl

end CFSG.KD.BrLy

end
