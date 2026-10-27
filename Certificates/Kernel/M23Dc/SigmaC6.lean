module

public import Certificates.Kernel.M23Dc.SigmaDefs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.M23Dc

theorem sig6 : sigK 6 = true := by
  quickRfl

end CFSG.KD.M23Dc

end
