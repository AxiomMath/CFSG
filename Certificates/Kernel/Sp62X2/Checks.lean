module

public import Certificates.Data.Kernel.Sp62X2K
public import Certificates.Kernel.Sp6Two.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp62X2

open CFSG.KD.Sp6Two

theorem ch4196_x2 : x2K REC 29 63 1 409 945 15 = true := by quickRfl

end CFSG.KD.Sp62X2

end
