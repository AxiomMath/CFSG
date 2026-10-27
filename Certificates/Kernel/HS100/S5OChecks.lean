module

public import Certificates.Kernel.HS100.S5OData
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Data.Kernel.Misc.PermWit
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS100

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum

theorem S5O.perm : allN 16
    (fun j => permOK 100 7 (mask 7) (100 * 7) (OX.F j) (pinvS 100 7 (mask 7) (OX.F j))) = true := by
  quickRfl

theorem S5O.permU : permOK 100 7 (mask 7) (100 * 7) (HP.F 15) (pinvS 100 7 (mask 7) (HP.F 15)) =
    true := by quickRfl

theorem S5O.sizes : (Nat.beq OS.N 1024 && Nat.beq OE.N 1344) = true := by quickRfl

theorem OS.keys : keysSK 100 7 [0, 1, 2, 3, 4] OS.N OS.T OS.SK = true := by quickRfl

theorem OE.keys : keysSK 100 7 [0, 1, 2, 3, 4] OE.N OE.T OE.SK = true := by quickRfl

theorem S5O.gens : ((allN 4 fun k => Nat.beq (OS.G k) (OX.F k)) &&
    allN 2 fun k => Nat.beq (OE.G k) (OX.F (k + 14))) = true := by quickRfl

theorem S5O.gensP : allN 4 (fun k => (rngK (OX.F k) && inHS (OX.F k)) ||
    (rngK (pm (HP.F 15) (OX.F k)) && inHS (pm (HP.F 15) (OX.F k)))) = true := by quickRfl

theorem S5O.z : (rngK (OX.F 4) && inHS (OX.F 4) && !Nat.beq (OX.F 4) (pidn 100 7) &&
    Nat.beq (pm (OX.F 4) (OX.F 4)) (pidn 100 7)) = true := by quickRfl

theorem S5O.os : allN 1024 osOne = true := by quickRfl

theorem S5O.y : (rngK (OX.F 5) && !inHS (OX.F 5) && Nat.beq (pm (OX.F 5) (OX.F 5)) (pidn 100 7) &&
    memK 1024 OS.T (OX.F 5) && memK 1024 OS.T (OX.F 6) &&
    Nat.beq (pm (OX.F 6) (OX.F 5)) (pm (pm (OX.F 5) (OX.F 4)) (OX.F 6))) = true := by quickRfl

theorem S5O.xs : allN 7 (fun i => rngK (OX.F (i + 7)) && inHS (OX.F (i + 7)) &&
    Nat.beq (pm (OX.F (i + 7)) (OX.F 5)) (pm (OX.F 5) (OX.F (i + 7)))) = true := by quickRfl

theorem S5O.cox : ((allN 7 fun i => Nat.beq (pm (OX.F (i + 7)) (OX.F (i + 7))) (pidn 100 7)) &&
    (allN 6 fun i => Nat.beq (pm (pm (OX.F (i + 7)) (OX.F (i + 8))) (OX.F (i + 7)))
      (pm (pm (OX.F (i + 8)) (OX.F (i + 7))) (OX.F (i + 8)))) &&
    (allN 7 fun i => allN 7 fun j => decide (j < i + 2) ||
      Nat.beq (pm (OX.F (i + 7)) (OX.F (j + 7))) (pm (OX.F (j + 7)) (OX.F (i + 7))))) = true := by
  quickRfl

theorem S5O.fix0 : Nat.beq (pg 7 (mask 7) (OX.F 5) 0) 0 = true := by quickRfl

theorem S5O.fixCnt : Nat.beq (CFSG.KC.PermWit.cntK 100 (fun q => Nat.beq (pg 7 (mask 7) (OX.F 5) q) q &&
    Nat.blt (rpos 7 (mask 7) (100 * 7) (HC.LR 0) q) (rcnt (HC.LR 0)))) 30 = true := by quickRfl

theorem S5O.zw : (Nat.beq (CFSG.EvenSporadicStandard.HSStd.s5oZWord.foldl
      (fun acc i => pm acc (OX.F (i + 7))) (pidn 100 7)) (OX.F 4) &&
    Nat.beq (pm (OX.F 8) (OX.F 4)) (pm (OX.F 4) (OX.F 8)) &&
    Nat.beq (pm (OX.F 4) (OX.F 5)) (pm (OX.F 5) (OX.F 4))) = true := by quickRfl

end CertificateChecks.KernelHS100

end
