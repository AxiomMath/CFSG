module

public import Certificates.Kernel.SporSch.Ru.LA2254
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Ru.CChain
public import Certificates.Kernel.SporSch.Ru.LChain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuLA

open CFSG.KC.Enum

theorem comm : commOK = true := by quickRfl

theorem fix : allN 19 fixOK = true := by quickRfl

end CertificateChecks.KernelSporSch.RuLA

end
