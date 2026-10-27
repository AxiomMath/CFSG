module

public import Certificates.Kernel.Sp4Ov.Data
public import Certificates.Kernel.Sp4Ov.LinesData
public import Certificates.Kernel.Sp4Ov.SpecData
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.Sp4Ov

theorem ch7138_special : specialK D.spM D.spec D.a36L D.b36L D.s36L D.s120L D.p9L D.spL D.p9M
    D.permL D.psiInvT D.ptT = true := by
  quickRfl

end CFSG.KD.Sp4Ov

end
