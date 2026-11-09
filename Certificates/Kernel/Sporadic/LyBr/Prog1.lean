module

public import CFSG.Certificates.Kernel.Orders.Cert
public import Certificates.Kernel.Sporadic.LyBr.Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#kc_repo #kc_json CFSG.KD.BrLy "Certificates/Kernel/Sporadic/LyBr/data/hm.json" 58075
  10662110596787591430 (HM1 : List Nat)

public noncomputable section

namespace CFSG.KD.BrLy

theorem hm1_0 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM1.drop 0).take 6) (nat_lit 1303))
    (nat_lit 1447) = true := by
  quickRfl

theorem hm1_1 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM1.drop 6).take 6) (nat_lit 1447))
    (nat_lit 1591) = true := by
  quickRfl

theorem hm1_2 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM1.drop 12).take 6) (nat_lit 1591))
    (nat_lit 1735) = true := by
  quickRfl

theorem hm1_3 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM1.drop 18).take 6) (nat_lit 1735))
    (nat_lit 1879) = true := by
  quickRfl

theorem hm1_4 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM1.drop 24).take 6) (nat_lit 1879))
    (nat_lit 2023) = true := by
  quickRfl

theorem hm1_5 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM1.drop 30).take 6) (nat_lit 2023))
    (nat_lit 2167) = true := by
  quickRfl

theorem hm1_6 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM1.drop 36).take 6) (nat_lit 2167))
    (nat_lit 2311) = true := by
  quickRfl

theorem hm1_7 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM1.drop 42).take 6) (nat_lit 2311))
    (nat_lit 2455) = true := by
  quickRfl

theorem hm1_8 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM1.drop 48).take 6) (nat_lit 2455))
    (nat_lit 2599) = true := by
  quickRfl

end CFSG.KD.BrLy

end
