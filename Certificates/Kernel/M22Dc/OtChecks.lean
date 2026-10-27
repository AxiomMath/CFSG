module

public import Certificates.Kernel.M22Dc.OtDefs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.M22Dc

theorem ots : (List.range 5).all otOK = true := by
  quickRfl

end CFSG.KD.M22Dc

end
