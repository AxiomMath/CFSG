module

public import Certificates.Data.Kernel.Sp62Pk
public import Certificates.Kernel.Sp6A2.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp6A2

open CFSG.KD.Sp62

theorem tabX0_799751 : (Nat.beq (recX REC 5126 0) ONE &&
    tableK REC (rmulSt (at2 REC 0)) 5126 168 3 6 3) = true := by quickRfl
theorem tabX1_799751 : (Nat.beq (recX REC 5295 0) ONE &&
    tableK REC (rmulSt (at2 REC 2)) 5295 168 3 6 3) = true := by quickRfl
theorem tabX2_799751 : (Nat.beq (recX REC 5464 0) ONE &&
    tableK REC (rmulSt (at2 REC 4)) 5464 168 3 6 3) = true := by quickRfl
theorem tabS0_799751 : (Nat.beq (recX REC 5633 0) ONE &&
    tableK REC (rmulSt (at2 REC 6)) 5633 6 1 1 1) = true := by quickRfl
theorem tabS1_799751 : (Nat.beq (recX REC 5640 0) ONE &&
    tableK REC (rmulSt (at2 REC 8)) 5640 6 1 1 1) = true := by quickRfl
theorem tabS2_799751 : (Nat.beq (recX REC 5647 0) ONE &&
    tableK REC (rmulSt (at2 REC 10)) 5647 6 1 1 1) = true := by quickRfl
theorem tabK4_799751 : (Nat.beq (recX REC 5654 0) ONE &&
    tableK REC (rmulSt (at2 REC 12)) 5654 6 1 1 1) = true := by quickRfl
theorem tabK2_799751 : (Nat.beq (recX REC 5661 0) ONE &&
    tableK REC (rmulSt (at2 REC 14)) 5661 6 1 1 1) = true := by quickRfl
theorem tabD_799751 : (Nat.beq (recX REC 5668 0) ONE &&
    tableK REC (rmulSt (at2 REC 16)) 5668 36 1 2 1) = true := by quickRfl
theorem tabC7_799751 : (Nat.beq (recX REC 5705 0) ONE &&
    tableK REC (rmulSt (at2 REC 18)) 5705 648 11 21 11) = true := by quickRfl

end CFSG.KD.Sp6A2

end
