module

public import Certificates.Kernel.SporSch.J1.Levels
public import Certificates.Data.Kernel.SporSch.MathieuOC
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC

theorem sz7400 : szOK 3080 12 = true := by quickRfl

theorem words7400 : wordOrdK 3080 12 (mask 12) (pidn 3080 12) 2 3
    [([3, 0, 1, 0, 3, 2, 1, 2], 19), ([3, 0, 1, 2], 19)] (J1L.S 0) (J1L.S 1) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.J1

end
