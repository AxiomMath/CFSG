module

public import Certificates.Kernel.GL62.Data
public import Certificates.Data.Kernel.GL62.Check
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KC.GL62.Checks

open CFSG.KD.GL62

theorem ch36405_b : bK BL BIL BP BIP BT = true := by quickRfl

theorem ch36405_ord : ordK RC = true := by quickRfl

theorem ch36405_rc0 : rcK BP BIP (headsK GD) (nthK RC List.nil 0) = true := by quickRfl
theorem ch36405_rc1 : rcK BP BIP (headsK GD) (nthK RC List.nil 1) = true := by quickRfl
theorem ch36405_rc2 : rcK BP BIP (headsK GD) (nthK RC List.nil 2) = true := by quickRfl
theorem ch36405_rc3 : rcK BP BIP (headsK GD) (nthK RC List.nil 3) = true := by quickRfl
theorem ch36405_rc4 : rcK BP BIP (headsK GD) (nthK RC List.nil 4) = true := by quickRfl
theorem ch36405_rc5 : rcK BP BIP (headsK GD) (nthK RC List.nil 5) = true := by quickRfl
theorem ch36405_rc6 : rcK BP BIP (headsK GD) (nthK RC List.nil 6) = true := by quickRfl
theorem ch36405_rc7 : rcK BP BIP (headsK GD) (nthK RC List.nil 7) = true := by quickRfl
theorem ch36405_rc8 : rcK BP BIP (headsK GD) (nthK RC List.nil 8) = true := by quickRfl
theorem ch36405_rc9 : rcK BP BIP (headsK GD) (nthK RC List.nil 9) = true := by quickRfl
theorem ch36405_rc10 : rcK BP BIP (headsK GD) (nthK RC List.nil 10) = true := by quickRfl
theorem ch36405_rc11 : rcK BP BIP (headsK GD) (nthK RC List.nil 11) = true := by quickRfl
theorem ch36405_rc12 : rcK BP BIP (headsK GD) (nthK RC List.nil 12) = true := by quickRfl

theorem ch36405_rcLen : Nat.beq (lenK RC) 13 = true := by quickRfl

theorem ch36405_good : goodK BP BIP GD = true := by quickRfl

theorem ch36405_comm : commK GD C = true := by quickRfl

theorem ch36405_hit0 : hitK BP GD HB H HW 0 = true := by quickRfl
theorem ch36405_hit1 : hitK BP GD HB H HW 1 = true := by quickRfl
theorem ch36405_hit2 : hitK BP GD HB H HW 2 = true := by quickRfl
theorem ch36405_hit3 : hitK BP GD HB H HW 3 = true := by quickRfl
theorem ch36405_hit4 : hitK BP GD HB H HW 4 = true := by quickRfl
theorem ch36405_hit5 : hitK BP GD HB H HW 5 = true := by quickRfl
theorem ch36405_hit6 : hitK BP GD HB H HW 6 = true := by quickRfl
theorem ch36405_hit7 : hitK BP GD HB H HW 7 = true := by quickRfl
theorem ch36405_hit8 : hitK BP GD HB H HW 8 = true := by quickRfl
theorem ch36405_hit9 : hitK BP GD HB H HW 9 = true := by quickRfl
theorem ch36405_hit10 : hitK BP GD HB H HW 10 = true := by quickRfl
theorem ch36405_hit11 : hitK BP GD HB H HW 11 = true := by quickRfl
theorem ch36405_hit12 : hitK BP GD HB H HW 12 = true := by quickRfl
theorem ch36405_hit13 : hitK BP GD HB H HW 13 = true := by quickRfl
theorem ch36405_hit14 : hitK BP GD HB H HW 14 = true := by quickRfl
theorem ch36405_hit15 : hitK BP GD HB H HW 15 = true := by quickRfl
theorem ch36405_hit16 : hitK BP GD HB H HW 16 = true := by quickRfl

theorem ch36405_hb : hbK BP GD HB = true := by quickRfl

theorem ch36405_elim : elimK GD H C = true := by quickRfl

theorem ch36405_fam : famK BP GD F = true := by quickRfl

end CFSG.KC.GL62.Checks

end
