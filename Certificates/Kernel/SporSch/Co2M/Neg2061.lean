
module

public import Certificates.Kernel.SporSch.Co2M.ThirdCnt
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2Third

theorem neg_fixList : not (fixListK 2300 12 (mask 12) (UP 0) fxP 51) = true := by quickRfl

theorem neg_cand : not (Nat.beq (candK 2300 12 (mask 12) (2300 * 12) Co2T3.S Co2T3.SI 30 (t3St 1)
    (Co2T3.LR 1) inO42 fxP 52 (Nat.succ (mIK 2300 12 (mask 12) (2300 * 12) Co2T3.S Co2T3.SI 30
      (t3St 1) (Co2T3.LR 1) inO42 fxP 52 0))) 18) = true := by quickRfl

theorem neg_clos : not (closK 12 (mask 12) Co2T3.S Co2T3.SI 30 (t3St 2) oP 41) = true := by
  quickRfl

theorem neg_fixCnt : not (Nat.beq (fixCntK 12 (mask 12) (Co2T3.LR 2) (pidn 2300 12)) 32) = true := by
  quickRfl

theorem neg_inK : not (inK oP 42 0) = true := by quickRfl

theorem neg_mIK : not (Nat.beq (mIK 2300 12 (mask 12) (2300 * 12) Co2T3.S Co2T3.SI 30 (t3St 0)
    (Co2T3.LR 0) inO1 fxP 52 154) (mIK 2300 12 (mask 12) (2300 * 12) Co2T3.S Co2T3.SI 30
      (t3St 0) (Co2T3.LR 0) inO1 fxP 52 0)) = true := by quickRfl

end CertificateChecks.KernelSporSch.Co2M

end
