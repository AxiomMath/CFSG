module

public import Certificates.Kernel.SporSch.Ly.SylTab
public import Certificates.Kernel.SporSch.Ly.GLQData
public import Certificates.Data.Kernel.SporSch.LyGLQ
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
namespace CertificateChecks.KernelSporSch.LyGQ

open CFSG.KC.Enum CFSG.KS.SporSch.LySyl CFSG.KS.SporSch.LyGLQ

theorem invo : Nat.beq (invoCnt LySt.MT W (pairsK LySt.MT) A) 176 = true := by quickRfl

end CertificateChecks.KernelSporSch.LyGQ

end
