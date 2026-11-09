module

public import Certificates.Data.Kernel.PermCent.B0Walk

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.B0T

open CFSG.ComponentClassification.CatFactsSmall.PSp43 Certificates.OmegaB0 CFSG.KC.Enum

theorem kFix : fixS fB blC blC = true := by decide +kernel

theorem kLenP : lvCP.length = 4 := by decide +kernel

theorem kLenA : lvCA.length = 4 := by decide +kernel

theorem kMaskP : masksS fB (lvCP.zip mskP) = true := by decide +kernel

theorem kMaskA : masksS fB (lvCA.zip mskA) = true := by decide +kernel

theorem kW1 : walkS (act1T ((bl ()).map cOf)) (lvCP.zip mskP) 1 ptsB = true := by
  decide +kernel

theorem kW2 : walkS (act2Q ((bl ()).map cOf)) (lvCA.zip mskA) 1 ptsB = true := by
  decide +kernel

theorem kW3 : strictB (walkF (bits3T ((bl ()).map cOf)) (lvCP.zip mskP) 1 ptsB 0)
    (fun r => coverF (fun σ => decide (Equiv.Perm.sign σ = 1)) r (s5l ()) 0) = true := by
  decide +kernel

theorem kAct : actC (elemsC QP45) (elemsC QA45) ((bl ()).map cOf) phC blC (allVecs ()) (s5l ()) =
    true := by
  have hP : (lvCP.zip mskP).map Prod.fst = lvCP := List.map_fst_zip (by rw [kLenP]; rfl)
  have hA : (lvCA.zip mskA).map Prod.fst = lvCA := List.map_fst_zip (by rw [kLenA]; rfl)
  have h1 := filter_all_of_walk kFix _ kMaskP _ kW1
  have h2 := filter_all_of_walk kFix _ kMaskA _ kW2
  have h3 := cover_of_walkT _ kW3
  have h1' := List.all_eq_true.2 fun g hg => act1T_sound g (List.all_eq_true.1 h1 g hg)
  have h2' := List.all_eq_true.2 fun g hg => act2T_sound g
    (act2T_of_act2Q _ g (List.all_eq_true.1 h2 g hg))
  rw [hP] at h1' h3
  rw [hA] at h2'
  rw [elemsC_eq_levelsC, elemsC_eq_levelsC, levelsC_QP45, levelsC_QA45]
  exact actC_of _ _ _ _ _ _ _ h1' h2' h3

end CFSG.Certificates.Kernel.PkCV.B0T
