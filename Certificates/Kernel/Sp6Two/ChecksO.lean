module

public import Certificates.Data.Kernel.Sp62Pk
public import Certificates.Kernel.Sp6Two.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp6Two

open CFSG.KD.Sp62

theorem tabO0_ok : (Nat.beq (recX REC 29 0) (REC 25) &&
    tableK REC (conjSt (at2 REC 21) (at2 REC 23)) 29 63 1 2 1) = true := by quickRfl
theorem tabO1_ok : (Nat.beq (recX REC 93 0) (REC 26) &&
    tableK REC (conjSt (at2 REC 21) (at2 REC 23)) 93 315 5 10 5) = true := by quickRfl
theorem tabO2_ok : (Nat.beq (recX REC 409 0) (REC 27) &&
    tableK REC (conjSt (at2 REC 21) (at2 REC 23)) 409 945 15 30 15) = true := by quickRfl
theorem tabO3_ok : (Nat.beq (recX REC 1355 0) (REC 28) &&
    tableK REC (conjSt (at2 REC 21) (at2 REC 23)) 1355 3780 60 119 60) = true := by quickRfl

end CFSG.KD.Sp6Two

end
