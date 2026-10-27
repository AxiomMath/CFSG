module

public import Certificates.Data.Kernel.W4C1K
public import Certificates.Kernel.Sp6Two.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.W4C1

open CFSG.KD.Sp62 CFSG.KD.Sp6Two

theorem chain330375_ok :
    chainK REC 34728 (at2 REC 16) (recX REC 34728 158) 8 = true := by quickRfl

end CFSG.KD.W4C1

end
