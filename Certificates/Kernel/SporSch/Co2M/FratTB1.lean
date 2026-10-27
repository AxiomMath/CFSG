
module

public import Certificates.Kernel.SporSch.Co2M.FratD
public import Certificates.Kernel.SporSch.Co2M.FratTr
public import Certificates.Kernel.SporSch.Co2M.Seeds
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS.Co2M

theorem tb1 : allN 64 (fun k => bindK (PV 0) (Co2LF.TR (Nat.add 64 k)) (FT0.getD (Nat.add 64 k) 0)
    (FT0I.getD (Nat.add 64 k) 0)) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.Co2M

end
