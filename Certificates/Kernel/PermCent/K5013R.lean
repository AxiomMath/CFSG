module

public import Certificates.Data.Kernel.PermCent.KGrpC3
public import CFSG.GH74.KGroups.M11Inputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5013R

open CFSG.GH74.KGroups.M11 CFSG.Sporadic.Mathieu

theorem k5013r : q8c2atC (cOf m11gA) ((elemsC Q).filter fun g => eq22C g (cOf m11gA)
    (cOf m11gA) g) = true := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5013R

end
