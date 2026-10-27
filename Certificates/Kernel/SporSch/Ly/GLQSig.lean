module

public import Certificates.Kernel.SporSch.Ly.SylTab
public import Certificates.Kernel.SporSch.Ly.GLQData
public import Certificates.Data.Kernel.SporSch.LyGLQ
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
namespace CertificateChecks.KernelSporSch.LyGQ

open CFSG.KC.Enum CFSG.KS.SporSch.LySyl CFSG.KS.SporSch.LyGLQ

theorem sig : allN 256 (sigQ LySt.MT SG) = true := by quickRfl

theorem assoc : allN 3 (assocQ LySt.MT) = true := by quickRfl

end CertificateChecks.KernelSporSch.LyGQ

end
