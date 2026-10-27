module

public import Certificates.Data.Kernel.PermCent.Gs03C
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03U33Data

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.Gs03.K1037402

open CFSG.GH74.KGroups.U33 CFSG.LocalAnalysis.WeakClosure81.Gs03U33

theorem kReps : (u33Classes.map fun c => c.1).map cOf = [pu, pt2].map cOf := by
  decide +kernel

theorem kCls : clsesC QP ([pa, pb].map cOf) 4 (u33Classes.map cOfCls) = true := by
  decide +kernel

end CFSG.Certificates.Kernel.PkCV.Gs03.K1037402

end
