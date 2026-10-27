module

public import Certificates.Data.Kernel.Sp62Pk
public import Certificates.Kernel.Sp62.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp62

theorem tabO0_ok : (Nat.beq (recX REC 6739 0) (REC 33) &&
    tableK REC (conjSt (at2 REC 10) (at2 REC 12)) 6739 672 11 21 11) = true := by quickRfl
theorem tabO1_ok : (Nat.beq (recX REC 7412 0) (REC 34) &&
    tableK REC (conjSt (at2 REC 10) (at2 REC 12)) 7412 672 11 21 11) = true := by quickRfl
theorem tabO2_ok : (Nat.beq (recX REC 8085 0) (REC 35) &&
    tableK REC (conjSt (at2 REC 10) (at2 REC 12)) 8085 672 11 21 11) = true := by quickRfl

end CFSG.KD.Sp62

end
