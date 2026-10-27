module

public import Certificates.Kernel.W4Row.HS119Tabs
public import Certificates.Kernel.W4Row.HS119CTabs
public import Certificates.Data.Kernel.W4Row.HS119CK
public import Certificates.Kernel.LocalQT.SV.C4126T
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HS119

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.HS119 CFSG.KD.LQT.C4126

@[expose] noncomputable def evH : Nat → Nat → Nat :=
  evL SPA (fun l => HC.F (Nat.succ l)) (fun l => HCI (Nat.succ l)) HS.F HSI

theorem c_dep : allN 1024 (depAt SPA) = true := by quickRfl

theorem c_inc : andB (allN 266 (lIncAt LS)) (allN 56 (lIncAt LP)) = true := by quickRfl

theorem c_z : zAt evH (HZ 1) (HZ 0) = true := by quickRfl

theorem c_cos : andB (Nat.beq (GO 0) 6)
    (allN 4 (cosAt evH (fun l => HC.F (Nat.succ l)) KW (GO 0) (HZ 1) (HZ 0))) = true := by
  quickRfl

theorem c_s0 : allR 0 150 (slotS evH SPA II HS.F CH CW CV CY RS LS (GO 0) (HZ 1)) = true := by
  quickRfl

theorem c_s1 : allR 150 50 (slotS evH SPA II HS.F CH CW CV CY RS LS (GO 0) (HZ 1)) = true := by
  quickRfl

theorem c_s2 : allR 200 66 (slotS evH SPA II HS.F CH CW CV CY RS LS (GO 0) (HZ 1)) = true := by
  quickRfl

theorem c_p : allN 56 (slotP evH SPA II HS.F CH CW CV CY RP LP (GO 0) (HZ 1) 266) = true := by
  quickRfl

end CFSG.KD.HS119

end
