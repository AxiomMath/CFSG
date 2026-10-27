module

public import Certificates.Kernel.LocalQT.Base.C4133D
public import Certificates.Kernel.LocalQT.Base.C4140
public import Certificates.Data.Kernel.LocalQT.X1H
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HSCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PipeNative
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHS

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4133

open CFSG.KC.LQT.XH CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Setup.X1

theorem hd : x1HH 1100 11 C4140.ta C4140.tb hsProg2 hsQp 289 339 296 377 9 100000 512 [G0, G1, G2]
    Z1L Z2L Z3L QcL GC GIC HC HIC = true := by
  quickRfl

end CFSG.KD.LQT.C4133

end
