module

public import Certificates.Data.Kernel.Sp6TwoK
public import Certificates.Kernel.Sp6Two.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp6Two

open CFSG.KD.Sp62

theorem tabC1_ok : (Nat.beq (recX REC 28177 0) ONE &&
    tableK REC (rmulSt (at2 REC 2)) 28177 4608 72 144 72) = true := by quickRfl
theorem tabC2_ok : (Nat.beq (recX REC 32786 0) ONE &&
    tableKG REC (rmulSt (at2 REC 4)) 32786 1536 4 24 96 24) = true := by quickRfl
theorem tabC3_ok : (Nat.beq (recX REC 34323 0) ONE &&
    tableKG REC (rmulSt (at2 REC 8)) 34323 384 4 6 24 6) = true := by quickRfl
theorem tabP0_ok : (Nat.beq (recX REC 34708 0) ONE &&
    tableK REC (rmulSt (at2 REC 12)) 34708 9 1 1 1) = true := by quickRfl
theorem tabP1_ok : (Nat.beq (recX REC 34718 0) ONE &&
    tableK REC (rmulSt (at2 REC 14)) 34718 9 1 1 1) = true := by quickRfl
theorem tabS_ok : (Nat.beq (recX REC 34728 0) ONE &&
    tableKG REC (rmulSt (at2 REC 16)) 34728 512 5 8 40 8) = true := by quickRfl

end CFSG.KD.Sp6Two

end
