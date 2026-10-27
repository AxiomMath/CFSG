module

public import Certificates.Data.Kernel.Sp62Pk
public import Certificates.Kernel.Sp62.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp62

theorem tabC0_ok : (Nat.beq (recX REC 38 0) ONE &&
    tableK REC (rmulSt (at2 REC 0)) 38 2160 34 68 34) = true := by quickRfl
theorem tabC1_ok : (Nat.beq (recX REC 2199 0) ONE &&
    tableK REC (rmulSt (at2 REC 2)) 2199 2160 34 68 34) = true := by quickRfl
theorem tabC2_ok : (Nat.beq (recX REC 4360 0) ONE &&
    tableK REC (rmulSt (at2 REC 4)) 4360 2160 34 68 34) = true := by quickRfl
theorem tabC3_ok : (Nat.beq (recX REC 6521 0) ONE &&
    tableK REC (rmulSt (at2 REC 6)) 6521 108 2 4 2) = true := by quickRfl
theorem tabC4_ok : (Nat.beq (recX REC 6630 0) ONE &&
    tableK REC (rmulSt (at2 REC 8)) 6630 108 2 4 2) = true := by quickRfl

end CFSG.KD.Sp62

end
