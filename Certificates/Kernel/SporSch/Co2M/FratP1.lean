
module

public import Certificates.Kernel.SporSch.Co2M.FratTr
public import Certificates.Data.Kernel.SporSch.Co2Prof
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KS.Co2P CFSG.Sporadic.Co2Schreier

theorem prof1 : profAll (FYZ.getD 32 0) (fun w => FYZ.getD w 0) FT0 FT1 profTable 8 8 = true := by
  quickRfl

end CertificateChecks.KernelSporSch.Co2M

end
