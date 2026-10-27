module

public import Certificates.Kernel.SuzThree13637.ClsData
public import Certificates.Data.Kernel.Spor.HypK
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.SuzThree13637

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem y_ok : (Nat.beq (pcomp 1782 11 (mask 11) CD.Y CD.Y2) CD.I &&
    Nat.beq (pg 11 (mask 11) CD.Y 0) 1) = true := by quickRfl

end CFSG.KD.SuzThree13637

end
