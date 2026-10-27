module

public import Certificates.Kernel.W4Row.HS119Tabs
public import Certificates.Data.Kernel.W4Row.HS119K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HS119

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.HS119

theorem x_r0 : andB (Nat.beq (RS 0) 1) (Nat.beq (RP 0) 1) = true := by quickRfl

theorem x_ls : andB (allN 266 (lsAt RS LS)) (allN 56 (lsAt RP LP)) = true := by quickRfl

theorem x_s0 : allR 0 70 (fun j => allN 192
    (extAt false SPA (GO 0) II PT IX CM CG RS LS XS 266 j)) = true := by quickRfl

theorem x_s1 : allR 70 70 (fun j => allN 192
    (extAt false SPA (GO 0) II PT IX CM CG RS LS XS 266 j)) = true := by quickRfl

theorem x_s2 : allR 140 126 (fun j => allN 192
    (extAt false SPA (GO 0) II PT IX CM CG RS LS XS 266 j)) = true := by quickRfl

theorem x_p : allN 56 (fun j => allN 192
    (extAt true SPA (GO 0) II PT IX CM CG RP LP XP 56 j)) = true := by quickRfl

end CFSG.KD.HS119

end
