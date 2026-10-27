
module

public import Certificates.Kernel.SporSch.Co2M.FratD
public import Certificates.Kernel.SporSch.Co2M.FratTr
public import Certificates.Kernel.SporSch.Co2M.Seeds
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS.Co2M

theorem tb2 : allN 64 (fun k => bindK (PV 0) (Co2LF.TR (Nat.add 128 k)) (FT1.getD k 0)
    (FT1I.getD k 0)) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.Co2M

end
