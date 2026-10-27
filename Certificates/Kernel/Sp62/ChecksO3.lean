module

public import Certificates.Data.Kernel.Sp62Pk
public import Certificates.Kernel.Sp62.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp62

theorem tabO3_ok : (Nat.beq (recX REC 8758 0) (REC 36) &&
    tableK REC (conjSt (at2 REC 10) (at2 REC 12)) 8758 13440 210 420 210) = true := by quickRfl

end CFSG.KD.Sp62

end
