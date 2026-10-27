module

public import Certificates.Kernel.LocalQT.Base.C4133D
public import Certificates.Data.Kernel.LocalQT.X1H
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4133

open CFSG.KC.LQT.XH

theorem nd : x1HN 1100 11 RC Z1L QcL GC GIC HC HIC = true := by
  quickRfl

end CFSG.KD.LQT.C4133

end
