
module

public import Certificates.Kernel.SporSch.Co2M.FratD
public import Certificates.Kernel.SporSch.Co2M.FratTr
public import Certificates.Kernel.SporSch.Co2M.FratMD
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS.Co2M

theorem yib : allN 32 (fun w => bindK (PV 0) (FY (Nat.add 32 w)) (yP w).2 (yP w).1) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.Co2M

end
