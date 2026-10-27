module

public import Certificates.Data.Kernel.ExcExt.Twin
public import Certificates.Kernel.ExcExt.Data
public import Certificates.Kernel.ExcExt.LineData
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.ExcExtK

set_option maxRecDepth 100000

theorem ch712526l5_4 : scanLineK D.T5 D5.L4 = true := by quickRfl

end CFSG.ExcExtK

end
