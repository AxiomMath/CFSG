
module

public import Certificates.Kernel.GH74Tab.B
public import Certificates.Kernel.GH74Tab.Claims
public import CFSG.Certificates.Kernel.GH74Tab.BSound
public import CFSG.Certificates.Kernel.GH74Tab.Adm

public section

namespace CFSG.KD.GH74Tab

open CFSG.KC.GH74Tab CFSG.GH74.GLS.C3.Layer2.Model

theorem c5038_claimB6 : (mkTab 6).claimB = true := by
  rw [claimB_eq]
  exact claimG_of_adm _ dat.adm c5042_claim6 fun _ hp =>
    bOK_sound c5042_trans6 c5042_data ((mkTab 6).valid_of_validB validB6) c5038_trans6 c5038_b hp

theorem c5038_claimB7 : (mkTab 7).claimB = true := by
  rw [claimB_eq]
  exact claimG_of_adm _ dat.adm c5042_claim7 fun _ hp =>
    bOK_sound c5042_trans7 c5042_data ((mkTab 7).valid_of_validB validB7) c5038_trans7 c5038_b hp

end CFSG.KD.GH74Tab

end
