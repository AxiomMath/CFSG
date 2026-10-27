module

public import Certificates.Kernel.Sporadic.Fi24G2d.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.Fi24G2d

theorem L.l2B : CFSG.KC.Fi24G2d.fixLOK F2B CFSG.KD.Fi24Fix.TG W2B 306936 504 = true := by quickRfl

theorem L.l2D : CFSG.KC.Fi24G2d.fixLOK F2D CFSG.KD.Fi24Fix.TG W2D 306936 696 = true := by quickRfl

end CFSG.KD.Fi24G2d

end
