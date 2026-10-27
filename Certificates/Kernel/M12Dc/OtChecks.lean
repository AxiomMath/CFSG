module

public import Certificates.Kernel.M12Dc.OtDefs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.M12Dc

theorem ots : (List.range 3).all otOK = true := by
  quickRfl

end CFSG.KD.M12Dc

end
