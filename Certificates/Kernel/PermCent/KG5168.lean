module

public import Certificates.Data.Kernel.PermCent.L34Outer3

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5168

open CFSG.GH74.KGroups.L34

theorem kHeis : heisC gA gB = true := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5168
