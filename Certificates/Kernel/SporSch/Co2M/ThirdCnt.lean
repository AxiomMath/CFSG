
module

public import Certificates.Kernel.SporSch.Co2M.ThirdBind
public import Certificates.Data.Kernel.SporSch.Co2Third
public meta import CFSG.Sporadic.Co2Schreier.ThirdCheckInputs
meta import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Misc.Perm.HexCmd

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.Sporadic.Co2Schreier

meta def t3Fix : Array (Array Nat) := #[(List.range 2300).toArray.filter fun x => uArr[x]! == x]

meta def t3O : Array (Array Nat) := #[#[49, 80, 215, 239, 294, 302, 410, 411, 418, 487, 563, 566,
  568, 577, 578, 670, 769, 770, 905, 942, 1016, 1053, 1083, 1146, 1159, 1220, 1367, 1404, 1485,
  1540, 1592, 1619, 1621, 1720, 1791, 1810, 1840, 1848, 1909, 1965, 2104, 2189]]

end CertificateChecks.KernelSporSch.Co2M

#kmisc_packarrs CertificateChecks.KernelSporSch.Co2M.FL CertificateChecks.KernelSporSch.Co2M.t3Fix 12
#kmisc_packarrs CertificateChecks.KernelSporSch.Co2M.OL CertificateChecks.KernelSporSch.Co2M.t3O 12

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2Third CFSG.Sporadic.Co2Schreier

@[expose] noncomputable def fxP (i : ℕ) : ℕ := pg 12 (mask 12) (FL 0) i

@[expose] noncomputable def oP (i : ℕ) : ℕ := pg 12 (mask 12) (OL 0) i

@[expose] noncomputable def t3St (i : ℕ) : ℕ := stepsAt 2300 12 Co2T3.S 30 Co2T3.BP i

@[expose] noncomputable def inO1 (y : ℕ) : Bool :=
  Nat.blt (rpos 12 (mask 12) (2300 * 12) (Co2T3.LR 1) y) (rcnt (Co2T3.LR 1))

@[expose] noncomputable def inO42 (y : ℕ) : Bool := inK oP 42 y

theorem t3fix_ok : fixListK 2300 12 (mask 12) (UP 0) fxP 52 = true := by quickRfl

theorem cand0_ok : Nat.beq (candK 2300 12 (mask 12) (2300 * 12) Co2T3.S Co2T3.SI 30 (t3St 0)
    (Co2T3.LR 0) inO1 fxP 52 (mIK 2300 12 (mask 12) (2300 * 12) Co2T3.S Co2T3.SI 30 (t3St 0)
      (Co2T3.LR 0) inO1 fxP 52 0)) 20 = true := by quickRfl

theorem cand1_ok : Nat.beq (candK 2300 12 (mask 12) (2300 * 12) Co2T3.S Co2T3.SI 30 (t3St 1)
    (Co2T3.LR 1) inO42 fxP 52 (mIK 2300 12 (mask 12) (2300 * 12) Co2T3.S Co2T3.SI 30 (t3St 1)
      (Co2T3.LR 1) inO42 fxP 52 0)) 18 = true := by quickRfl

theorem clos_ok : closK 12 (mask 12) Co2T3.S Co2T3.SI 30 (t3St 2) oP 42 = true := by quickRfl

@[expose] def fixCnts : List ℕ := [32, 8, 4, 1, 2, 1, 1, 1, 1, 1]

theorem cnt_ok : allN 10 (fun i => Nat.beq (fixCntK 12 (mask 12) (Co2T3.LR (Nat.add i 2)) (UP 0))
    (fixCnts.getD i 0)) = true := by quickRfl

theorem perm_ok : allN 30 (fun j => permOK 2300 12 (mask 12) (2300 * 12) (Co2T3.S j)
    (Co2T3.SI j)) = true := by quickRfl

theorem base_ok : allN 13 (fun t => Nat.beq (witRec.third.baseIndices.toArray[t]!)
    (pg 12 (mask 12) Co2T3.BP t)) = true := by quickRfl

@[expose] def t3Sizes : List ℕ := [2300, 891, 896, 96, 30, 1, 4, 1, 1, 1, 1, 1, 2]

theorem sizes_ok : allN 13 (fun j => Nat.beq (rcnt (Co2T3.LR j)) (t3Sizes.getD j 0)) = true := by
  quickRfl

theorem ufix_ok : allN 12 (fun t => Nat.beq (pg 12 (mask 12) (UP 0) (pg 12 (mask 12) Co2T3.BP t))
    (pg 12 (mask 12) Co2T3.BP t)) = true := by quickRfl

theorem move_ok : not (Nat.beq (pg 12 (mask 12) (UP 0) (pg 12 (mask 12) Co2T3.BP 12))
    (pg 12 (mask 12) Co2T3.BP 12)) = true := by quickRfl

end CertificateChecks.KernelSporSch.Co2M

end
