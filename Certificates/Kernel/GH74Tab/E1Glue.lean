module

public import Certificates.Kernel.GH74Tab.E1
public import Certificates.Kernel.GH74Tab.Claims
public import CFSG.Certificates.Kernel.GH74Tab.E1Sound
public import CFSG.Certificates.Kernel.GH74Tab.Adm

public section

namespace CFSG.KD.GH74Tab

open CFSG.KC.GH74Tab CFSG.GH74.GLS.C3.Layer2.Model

theorem c5042_e1P1_6 : (mkTab 6).claimG (mkTab 6).e1P1 = true :=
  claimG_of_adm _ dat.adm c5042_claim6 fun _ hp =>
    (e1OK_sound c5042_trans6 c5042_data c5042_e1_6 hp).1

theorem c5042_e1P1_7 : (mkTab 7).claimG (mkTab 7).e1P1 = true :=
  claimG_of_adm _ dat.adm7 c5042_claim7w fun _ hp =>
    (e1OK_sound c5042_trans7 c5042_data c5042_e1_7 hp).1

theorem c5042_e1P2_6 : (mkTab 6).claimG (mkTab 6).e1P2 = true :=
  claimG_of_adm _ dat.adm c5042_claim6 fun _ hp =>
    (e1OK_sound c5042_trans6 c5042_data c5042_e1_6 hp).2.1

theorem c5042_e1P2_7 : (mkTab 7).claimG (mkTab 7).e1P2 = true :=
  claimG_of_adm _ dat.adm7 c5042_claim7w fun _ hp =>
    (e1OK_sound c5042_trans7 c5042_data c5042_e1_7 hp).2.1

theorem c5042_e1P3_6 : (mkTab 6).claimG (mkTab 6).e1P3 = true :=
  claimG_of_adm _ dat.adm c5042_claim6 fun _ hp =>
    (e1OK_sound c5042_trans6 c5042_data c5042_e1_6 hp).2.2

theorem c5042_e1P3_7 : (mkTab 7).claimG (mkTab 7).e1P3 = true :=
  claimG_of_adm _ dat.adm7 c5042_claim7w fun _ hp =>
    (e1OK_sound c5042_trans7 c5042_data c5042_e1_7 hp).2.2

end CFSG.KD.GH74Tab

end
