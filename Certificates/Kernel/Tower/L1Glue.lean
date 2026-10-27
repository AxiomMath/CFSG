module

public import CFSG.Certificates.Kernel.Tower.L1Sound
public import Certificates.Kernel.Tower.WChecks
public import Certificates.Kernel.Tower.L1Checks

public section

namespace Certificates.KernelTower

open Certificates.KernelTower CFSG.OddStandard.AltStdSmall4.Tower

theorem sl_model : IsModel (⊤ : Subgroup (Grp slS)) 8192 (wm slSM slAC) subModel_sl.decW :=
  wm_model subModel_sl ch36409_lp ch36409_sm ch36409_ac

theorem wr_model : IsModel (⊤ : Subgroup (Grp wrS)) 8192 (wm wrSM wrAC) subModel_wr.decW :=
  wm_model subModel_wr ch36408_lp ch36408_sm ch36408_ac

theorem l1Facts_sl : L1Facts (Grp slS) (t₀ slS z0_mem_slS) := by
  have h := l1_sound sl_model ch36409_l1 ch36409_reps
  rwa [subModel_sl.decW_64 mat_sl1 z0_mem_slS] at h

theorem l1Facts_wr : L1Facts (Grp wrS) (t₀ wrS z0_mem_wrS) := by
  have h := l1_sound wr_model ch36408_l1 ch36408_reps
  rwa [subModel_wr.decW_64 mat_wr1 z0_mem_wrS] at h

end Certificates.KernelTower
