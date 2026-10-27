module

public import Certificates.Kernel.LocalComp.HeModelCheckDefs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.HexaKSound

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC.HeModelCheck

open CFSG.KC.Enum

theorem kOrb : allN 64 oAt = true := by quickRfl

end CertificateChecks.KernelLC.HeModelCheck

end
