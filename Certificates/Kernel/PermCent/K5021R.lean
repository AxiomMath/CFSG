module

public import Certificates.Data.Kernel.PermCent.KGrpC3
public import CFSG.GH74.KGroups.U33Inputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5021R

open CFSG.GH74.KGroups.U33

@[expose] noncomputable def reps : List (CV 28) := [cOf pu, cOf pt2]

theorem k5021r : reps.all (fun c => q8c2atC c ((elemsC QA).filter fun g => eq22C g c c g)) =
    true := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5021R

end
