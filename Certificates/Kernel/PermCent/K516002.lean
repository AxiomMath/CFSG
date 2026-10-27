module

public import Certificates.Data.Kernel.PermCent.S7M12C
public import Certificates.Data.S7Q8

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.K516002

open Certificates.S5Rows Certificates.S7Q8 CFSG.Certificates.Kernel.PkCV.S7M12C

theorem k516002_f2a : threeCycCheck (SLc.filter ord4B) CZc (fun _ => true) = true := by
  decide +kernel

theorem k516002_f2b : invPairCheck SLc fpC = true := by
  decide +kernel

end CFSG.Certificates.Kernel.PkCV.K516002

end
