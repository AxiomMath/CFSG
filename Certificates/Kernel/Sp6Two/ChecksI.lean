module

public import Certificates.Data.Kernel.Sp6TwoT
public import Certificates.Kernel.Sp6Two.Rec
public import Certificates.Kernel.Sp6Two.Idx
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp6Two

theorem invS_ok : invK6 REC IDX 34728 512 29 63 93 315 409 945 1355 3780 8 = true := by quickRfl

theorem two1_ok : centK6 REC 28177 4608 (REC 14) (REC 15) (REC 26) 72 = true := by quickRfl

end CFSG.KD.Sp6Two

end
