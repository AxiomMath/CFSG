module

public import Certificates.Kernel.GH74Tab.E23
public import Certificates.Kernel.GH74Tab.Claims
public import CFSG.Certificates.Kernel.GH74Tab.E23Sound
public import CFSG.Certificates.Kernel.GH74Tab.Adm

public section

namespace CFSG.KD.GH74Tab

open CFSG.KC.GH74Tab CFSG.GH74.GLS.C3.Layer2.Model

theorem c5043_admU : (dat.adm.all fun p => decide (p.2 < 64)) = true := by decide +kernel

theorem c5043_admU_of {p : Nat × Nat} (hp : p ∈ dat.adm) : p.2 < 64 := by
  have h := c5043_admU
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h p hp)

theorem c5043_e2P1_6 : (mkTab 6).claimG (mkTab 6).e2P1 = true :=
  claimG_of_adm _ dat.adm c5042_claim6 fun _ hp =>
    (e2OK_sound c5042_trans6 c5042_data c5043_e2 hp (c5043_admU_of hp)).1

theorem c5043_e2P1_7 : (mkTab 7).claimG (mkTab 7).e2P1 = true :=
  claimG_of_adm _ dat.adm c5042_claim7 fun _ hp =>
    (e2OK_sound c5042_trans7 c5042_data c5043_e2 hp (c5043_admU_of hp)).1

theorem c5043_e2P2_6 : (mkTab 6).claimG (mkTab 6).e2P2 = true :=
  claimG_of_adm _ dat.adm c5042_claim6 fun _ hp =>
    (e2OK_sound c5042_trans6 c5042_data c5043_e2 hp (c5043_admU_of hp)).2.1

theorem c5043_e2P2_7 : (mkTab 7).claimG (mkTab 7).e2P2 = true :=
  claimG_of_adm _ dat.adm c5042_claim7 fun _ hp =>
    (e2OK_sound c5042_trans7 c5042_data c5043_e2 hp (c5043_admU_of hp)).2.1

theorem c5043_e2P3_6 : (mkTab 6).claimG (mkTab 6).e2P3 = true :=
  claimG_of_adm _ dat.adm c5042_claim6 fun _ hp =>
    (e2OK_sound c5042_trans6 c5042_data c5043_e2 hp (c5043_admU_of hp)).2.2.1

theorem c5043_e2P3_7 : (mkTab 7).claimG (mkTab 7).e2P3 = true :=
  claimG_of_adm _ dat.adm c5042_claim7 fun _ hp =>
    (e2OK_sound c5042_trans7 c5042_data c5043_e2 hp (c5043_admU_of hp)).2.2.1

theorem c5043_e2P4_6 : (mkTab 6).claimG (mkTab 6).e2P4 = true :=
  claimG_of_adm _ dat.adm c5042_claim6 fun _ hp =>
    (e2OK_sound c5042_trans6 c5042_data c5043_e2 hp (c5043_admU_of hp)).2.2.2

theorem c5043_e2P4_7 : (mkTab 7).claimG (mkTab 7).e2P4 = true :=
  claimG_of_adm _ dat.adm c5042_claim7 fun _ hp =>
    (e2OK_sound c5042_trans7 c5042_data c5043_e2 hp (c5043_admU_of hp)).2.2.2

theorem c5044_e3P : (mkTab 7).claimG ((mkTab 7).e3P (mkTab 7).wActE3 (mkTab 7).wCommE3) = true :=
  claimG_of_adm _ dat.adm7 c5042_claim7w fun _ hp => e3OK_sound c5042_trans7 c5042_data c5044_e3 hp

end CFSG.KD.GH74Tab

end
