module

public import Certificates.Kernel.LocalQT.Base.C4133D
public import Certificates.Kernel.LocalQT.Base.C4140
public import Certificates.Data.Kernel.LocalQT.X1H
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HSData
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4133

open CFSG.KC.LQT.XH CFSG.QuasithinUnique.Setup.X1

theorem wd : x1HW 1100 11 hsWprog GC HC 1024 1026 C4140.ta C4140.tb = true := by
  quickRfl

end CFSG.KD.LQT.C4133

end
