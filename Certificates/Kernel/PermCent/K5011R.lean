module

public import Certificates.Data.Kernel.PermCent.KGrpC3
public import CFSG.GH74.KGroups.L33Inputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5011R

open CFSG.GH74.KGroups.L33

@[expose] noncomputable def reps : List (CV 26) := [cOf PA, cOf sg0 ^ 3]

theorem k5011r : reps.all (fun c => q8c2atC c ((elemsC QA).filter fun g => eq22C g c c g)) =
    true := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5011R

end
