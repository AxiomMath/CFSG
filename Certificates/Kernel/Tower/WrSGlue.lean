module

public import CFSG.Certificates.Kernel.Tower.CntSound
public import Certificates.Kernel.Tower.SGlue
public import Certificates.Kernel.Tower.WrSChecks

public section

namespace Certificates.KernelTower

open Certificates.KernelTower CFSG.OddStandard.AltStdSmall4.Tower

theorem ch36408_cz : czOK 8192 (wrSD 1) (wrSD 3) 0 152 = true :=
  czHB_czOK (by norm_num) ch36408_czH

theorem search_wr (α : MulAut (Grp wrS)) (hα : α (subModel_wr.decW 64) = subModel_wr.decW 64) :
    ∃ h : Grp wrS, h * subModel_wr.decW 64 = subModel_wr.decW 64 * h ∧ ∃ a < 96, ∀ i < 4,
      h * α (subModel_wr.decW (l16 wGS i)) * h⁻¹ =
        subModel_wr.decW (l16 (Nat.shiftRight wrIM (Nat.mul 64 a)) i) :=
  search_complete (W2 := fun r1 => wrSD (Nat.add 18 r1)) (W3 := fun r2 => wrSD (Nat.add 33 r2))
    wr_model ch36408_tree wGS_zero ch36408_ord ch36408_lab ch36408_cz ch36408_h ch36408_cm1
    ch36408_cm2 ch36408_cm3 ch36408_pv ch36408_lvl1 ch36408_lvl2 ch36408_lvl3 ch36408_r3
    ch36408_u2 α hα

end Certificates.KernelTower
