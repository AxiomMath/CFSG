module

public import Certificates.Data.Kernel.PermCent.KGrpC3
public import Certificates.Data.Kernel.PermCent.GoodC
public import CFSG.GH74.KGroups.M11Inputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K9740R

open CFSG.Certificates.Kernel.PkCV.Good CFSG.ClassicalInvolution.Q3.TA3.Check
  CFSG.GH74.KGroups.M11 CFSG.Sporadic.Mathieu

theorem k9740r : (noOddC 100 (centC (elemsC Q) (cOf m11gA)) &&
    pairsB (cOf m11gA) (centC (elemsC Q) (cOf m11gA))) = true := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K9740R

end
