module

public import Certificates.Kernel.HN1408.FixRYIDefs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.FixRDefs
public import Certificates.Kernel.HN1408.M11Words

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.FixR

theorem f3_yinv : yInvF Fix3.Y Fix3.YI 7 = true := by quickRfl
theorem f5a_yinv : yInvF Fix5a.Y Fix5a.YI 3 = true := by quickRfl
theorem f5b_yinv : yInvF Fix5b.Y Fix5b.YI 3 = true := by quickRfl
theorem f5c_yinv : yInvF Fix5c.Y Fix5c.YI 7 = true := by quickRfl
theorem f7_yinv : yInvF Fix7.Y Fix7.YI 125 = true := by quickRfl

end CFSG.KD.HN1408.FixR

end
