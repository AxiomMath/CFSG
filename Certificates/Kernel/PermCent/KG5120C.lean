module

public import Certificates.Data.Kernel.PermCent.L33AutTwin
public import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.L33A

open CFSG.GH74.KGroups.L33 CFSG.Certificates.Kernel.PkCV.KGrp

#kc_each e27B 0 8

theorem kLen : (elemsC QA).length ≤ 8 * 1404 := by decide +kernel

theorem kE27_neg : e27atC 1 (((elemsC QA).filter fun g => powOneC g 3).filter fun g =>
    eq22C g (cOf PB) (cOf PB) g) = false := by
  decide +kernel

end CFSG.Certificates.Kernel.PkCV.L33A
