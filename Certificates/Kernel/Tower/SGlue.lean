module

public import CFSG.Certificates.Kernel.Tower.SearchSound
public import Certificates.Kernel.Tower.L1Glue
public import Certificates.Kernel.Tower.AChecks
public import Certificates.Kernel.Tower.SChecks
public import Certificates.Kernel.Tower.SRangeChecks

public section

namespace Certificates.KernelTower

open Certificates.KernelTower CFSG.OddStandard.AltStdSmall4.Tower

theorem wGS_zero : l16 wGS 0 = 64 := by decide +kernel

theorem ch36409_cz : czOK 8192 (slSD 1) (slSD 3) 0 92 = true := by
  have h := allFrom_two ch36409_cz0 ch36409_cz1
  exact h

theorem ch36409_cm1' : cmOK 8192 (wm slSM slAC) 64 (slSD 0) (slSD 1) (slSD 3) (slSD 4) (l16 wGS 1)
    (lane (slSD 5) 8 255 0) (slSD 6) (slSD 9) 96 = true := ch36409_cm1

theorem ch36409_cm2' : cmOK 8192 (wm slSM slAC) 64 (slSD 0) (slSD 1) (slSD 3) (slSD 4) (l16 wGS 2)
    (lane (slSD 5) 8 255 1) (slSD 7) (slSD 10) 576 = true := ch36409_cm2

theorem ch36409_cm3' : cmOK 8192 (wm slSM slAC) 64 (slSD 0) (slSD 1) (slSD 3) (slSD 4) (l16 wGS 3)
    (lane (slSD 5) 8 255 2) (slSD 8) (slSD 11) 208 = true := ch36409_cm3

theorem ch36409_lvl2' : allB 6 (fun r1 => lvl2At (wm slSM slAC) 64 (slSD 0) (slSD 4) (slSD 7) 576
    (slSD 12) (slSD 14) (slSD 17) 672 (slSD (Nat.add 18 r1)) r1) = true := ch36409_lvl2

theorem ch36409_lvl3 : allFrom 0 672 (fun r2 => lvl3At (wm slSM slAC) 64 (slSD 0) (slSD 4) (slSD 8)
    208 (slSD 12) (slSD 14) (slSD 15) (slSD 17) 16128 (slSD (Nat.add 24 r2)) r2) = true := by
  have h := allFrom_two ch36409_lvl3_0 ch36409_lvl3_1
  exact h

theorem ch36409_r3 : allFrom 0 16128 slR3 = true := by
  have h₁ := allFrom_two ch36409_r3_0 ch36409_r3_1
  have h₂ := allFrom_two ch36409_r3_2 ch36409_r3_3
  have h := allFrom_two h₁ h₂
  exact h

theorem search_sl (α : MulAut (Grp slS)) (hα : α (subModel_sl.decW 64) = subModel_sl.decW 64) :
    ∃ h : Grp slS, h * subModel_sl.decW 64 = subModel_sl.decW 64 * h ∧ ∃ a < 32, ∀ i < 4,
      h * α (subModel_sl.decW (l16 wGS i)) * h⁻¹ =
        subModel_sl.decW (l16 (Nat.shiftRight slIM (Nat.mul 64 a)) i) :=
  search_complete (W2 := fun r1 => slSD (Nat.add 18 r1)) (W3 := fun r2 => slSD (Nat.add 24 r2))
    sl_model ch36409_tree wGS_zero ch36409_ord ch36409_lab ch36409_cz ch36409_h ch36409_cm1'
    ch36409_cm2' ch36409_cm3' ch36409_pv ch36409_lvl1 ch36409_lvl2' ch36409_lvl3 ch36409_r3
    ch36409_u2 α hα

end Certificates.KernelTower
