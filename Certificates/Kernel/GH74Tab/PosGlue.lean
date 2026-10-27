module

public import Certificates.Kernel.GH74Tab.Pos
public import Certificates.Kernel.GH74Tab.Claims
public import CFSG.Certificates.Kernel.GH74Tab.PosSound
public import CFSG.Certificates.Kernel.GH74Tab.Adm

public section

namespace CFSG.KD.GH74Tab

open CFSG.KC.GH74Tab CFSG.GH74.GLS.C3.Layer2.Model

theorem c5089_claimPosB6 : (mkTab 6).claimPosB = true := by
  rw [claimPosB_eq]
  exact claimG_of_adm _ dat.adm c5042_claim6 fun _ hp =>
    posOK_sound c5042_trans6 c5089_s2_6 c5089_pos hp _

theorem c5089_claimPosB7 : (mkTab 7).claimPosB = true := by
  rw [claimPosB_eq]
  exact claimG_of_adm _ dat.adm c5042_claim7 fun _ hp =>
    posOK_sound c5042_trans7 c5089_s2_7 c5089_pos hp _

end CFSG.KD.GH74Tab

end
