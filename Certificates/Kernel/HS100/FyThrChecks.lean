module

public import Certificates.Kernel.HS100.FyThrData
public import Certificates.Data.Kernel.Misc.PermWit
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS100

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin

theorem Fy.perm : allN 13
    (fun j => permOK 100 7 (mask 7) (100 * 7) (FT.F j) (pinvS 100 7 (mask 7) (FT.F j))) = true := by
  quickRfl

theorem Fy.fix0 : Nat.beq (pg 7 (mask 7) (FT.F 0) 0) 0 = true := by quickRfl

theorem Fy.fixCnt : Nat.beq (CFSG.KC.PermWit.cntK 100 (fun q => Nat.beq (pg 7 (mask 7) (FT.F 0) q) q &&
    Nat.blt (rpos 7 (mask 7) (100 * 7) (HC.LR 0) q) (rcnt (HC.LR 0)))) 10 = true := by quickRfl

theorem Fy.sizes : (Nat.beq FQ.N 9 && Nat.beq FE.N 36) = true := by quickRfl

theorem FQ.keys : keysSK 100 7 [0, 1, 2, 3, 4] FQ.N FQ.T FQ.SK = true := by quickRfl

theorem FE.keys : keysSK 100 7 [0, 1, 2, 3, 4] FE.N FE.T FE.SK = true := by quickRfl

theorem Fy.gens : (Nat.beq (FQ.G 0) (FT.F 0) && Nat.beq (FQ.G 1) (FT.F 1) &&
    allN 3 fun k => Nat.beq (FE.G k) (FT.F (k + 10))) = true := by quickRfl

theorem Fy.sift : allN 10 (fun j => Nat.beq (Nat.shiftRight (FT.F j) (100 * 7)) 0 &&
    allN 100 (fun t => Nat.blt (pg 7 (mask 7) (FT.F j) t) 100) &&
    siftK 100 7 (mask 7) (100 * 7) (pidn 100 7) HC.LR HC.TRI HC.BP 5 0 (FT.F j)) = true := by
  quickRfl

theorem Fy.trans : allN 9 (fun k => Nat.blt (FW k) 8 && (Nat.beq (FQ.T k) (pidn 100 7) ||
    Nat.beq (pcomp 100 7 (mask 7) (FT.F (FW k + 2)) (FT.F 0))
      (pcomp 100 7 (mask 7) (FQ.T k) (FT.F (FW k + 2))))) = true := by quickRfl

theorem Fy.rc : Nat.beq (rcnt (HC.LR 1)) 77 = true := by quickRfl

end CertificateChecks.KernelHS100

end
