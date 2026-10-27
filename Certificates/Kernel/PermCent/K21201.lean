module

public import Certificates.Data.Kernel.PermCent.U33Twin

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.U33T

open CFSG.GH74.KGroups.U33

theorem k21201 : elemC = true := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.U33T
