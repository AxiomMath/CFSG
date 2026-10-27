module

public import Certificates.Data.Kernel.PermCent.KGrpC2
public import Certificates.Data.Kernel.PermCent.KGrpC3
public import CFSG.GH74.KGroups.M11Inputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5097

open CFSG.GH74.KGroups.M11

theorem k5097 : oddCoreCheckC 495 (elemsC Q) (elemsC Q) = true := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5097
