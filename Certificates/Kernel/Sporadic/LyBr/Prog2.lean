module

public import CFSG.Certificates.Kernel.Orders.Cert
public import Certificates.Kernel.Sporadic.LyBr.Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#kc_repo #kc_json CFSG.KD.BrLy "Certificates/Kernel/Sporadic/LyBr/data/hm.json" 58075
  10662110596787591430 (HM2 : List Nat)

public noncomputable section

namespace CFSG.KD.BrLy

theorem hm2_0 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM2.drop 0).take 6) (nat_lit 2599))
    (nat_lit 2743) = true := by
  quickRfl

theorem hm2_1 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM2.drop 6).take 6) (nat_lit 2743))
    (nat_lit 2887) = true := by
  quickRfl

theorem hm2_2 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM2.drop 12).take 6) (nat_lit 2887))
    (nat_lit 3031) = true := by
  quickRfl

theorem hm2_3 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM2.drop 18).take 6) (nat_lit 3031))
    (nat_lit 3175) = true := by
  quickRfl

theorem hm2_4 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM2.drop 24).take 6) (nat_lit 3175))
    (nat_lit 3319) = true := by
  quickRfl

theorem hm2_5 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM2.drop 30).take 6) (nat_lit 3319))
    (nat_lit 3463) = true := by
  quickRfl

theorem hm2_6 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM2.drop 36).take 6) (nat_lit 3463))
    (nat_lit 3607) = true := by
  quickRfl

theorem hm2_7 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM2.drop 42).take 6) (nat_lit 3607))
    (nat_lit 3751) = true := by
  quickRfl

theorem hm2_8 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12)
    (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
    (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H) ONE ((HM2.drop 48).take 6) (nat_lit 3751))
    (nat_lit 3891) = true := by
  quickRfl

end CFSG.KD.BrLy

end
