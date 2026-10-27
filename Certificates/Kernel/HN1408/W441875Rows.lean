module

public import Certificates.Kernel.HN1408.W441875Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.W441875Data

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.W441875

open CFSG.KC.Enum CFSG.KS

theorem ch441875_rows : allN 3840 (rowK R RK) = true := by quickRfl

theorem ch441875_rowY : allN 15 (rowYK R RK RT Y YP CW) = true := by quickRfl

end CFSG.KD.HN1408.W441875

end
