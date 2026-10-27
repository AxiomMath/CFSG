module

public import Certificates.Data.Kernel.PermCent.GoodC
public import CFSG.GH74.KGroups.U33Inputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K9743R

open CFSG.Certificates.Kernel.PkCV.Good CFSG.ClassicalInvolution.Q3.TA3.Check
  CFSG.GH74.KGroups.U33

theorem k9743r : (noOddC 100 (centC (elemsC QP) (cOf pu)) &&
    pairsB (cOf pu) (centC (elemsC QP) (cOf pu))) = true := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K9743R

end
