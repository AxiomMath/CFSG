module

public import Certificates.Data.Kernel.Sp62Pk
public import Certificates.Kernel.Sp6Two.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp6Two

open CFSG.KD.Sp62

theorem tabC0_ok : (Nat.beq (recX REC 5136 0) ONE &&
    tableK REC (rmulSt (at2 REC 0)) 5136 23040 360 720 360) = true := by quickRfl

end CFSG.KD.Sp6Two

end
