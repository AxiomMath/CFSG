module

public import Certificates.Data.Kernel.Sp6TwoT
public import Certificates.Kernel.Sp6Two.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp6Two

theorem two0_ok : centK6 REC 5136 23040 (REC 12) (REC 13) (REC 25) 360 = true := by quickRfl

end CFSG.KD.Sp6Two

end
