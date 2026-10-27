module

public import Certificates.Kernel.Sporadic.Fi24G2e.OData
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public noncomputable section

namespace CFSG.KD.Fi24G2e.CL

open CFSG.KD.Fi24G2e CFSG.KD.Fi24G2d

theorem f0 : CFSG.KC.Fi24G2d.fixLOK F2D CFSG.KD.Fi24Fix.TG [0] 306936 696 = true := by quickRfl

theorem f2 : CFSG.KC.Fi24G2d.fixLOK F2D CFSG.KD.Fi24Fix.TG [2] 306936 696 = true := by quickRfl

theorem f4 : CFSG.KC.Fi24G2d.fixLOK F2D CFSG.KD.Fi24Fix.TG [4] 306936 696 = true := by quickRfl

theorem cl :
    CFSG.KC.Fi24G2e.clauseOK F2D CFSG.KD.Fi24Fix.TG CQL CYF 37886 37886 22978 22975 696 = true := by
  quickRfl

end CFSG.KD.Fi24G2e.CL

end
