
module

public import Certificates.Kernel.SporSch.Co2M.FratD
public import Certificates.Kernel.SporSch.Co2M.FratTr
public import Certificates.Kernel.SporSch.Co2M.FratMD
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS.Co2M

theorem sb : allN 16 (fun k => bindK (PV 0) (Co2LF.S k) (fratT.getD k (0, 0)).1
    (fratT.getD k (0, 0)).2) = true := by
  quickRfl

theorem yb : (allN 32 (fun w => bindK (PV 0) (FY w) (yP w).1 (yP w).2 &&
    Nat.beq (FYZ.getD w 0) (yP w).1) && Nat.beq (FYZ.getD 32 0) zP.1) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.Co2M

end
