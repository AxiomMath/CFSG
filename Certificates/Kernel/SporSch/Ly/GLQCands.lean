module

public import Certificates.Kernel.SporSch.Ly.SylTab
public import Certificates.Kernel.SporSch.Ly.GLQData
public import Certificates.Data.Kernel.SporSch.LyGLQ
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
namespace CertificateChecks.KernelSporSch.LyGQ

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.LySyl CFSG.KS.SporSch.LyGLQ

theorem alen : Nat.beq (lenL A) 512 = true := by quickRfl

theorem auts : (fun C => bAnd(Nat.beq (lenL C) 5632, autsK LySt.MT W C A)) (candsK LySt.MT SG) =
    true := by quickRfl

end CertificateChecks.KernelSporSch.LyGQ

end
