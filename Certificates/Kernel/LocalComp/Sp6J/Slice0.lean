module

public import Certificates.Kernel.LocalComp.Sp6J.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Sp6J

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.MOC

theorem kS0 : Nat.beq (cntOrdK 36 6 (mask 6) (36 * 6) (pidn 36 6) XQ.LR XQ.TR 6 One36 2 0) 763 =
    true := by quickRfl

end CertificateChecks.KernelLC.Sp6J

end
