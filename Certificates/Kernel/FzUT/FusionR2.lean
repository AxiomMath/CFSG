module

public import Certificates.Data.Kernel.FzUT.FusionP
public import Certificates.Kernel.FzUT.FusionD12

public section

namespace CFSG.KC.FzUT.R2

open CFSG.KD

theorem ch441790_r2_forest : forestOK 14765201 528900 270600 Fu2.FR = true := by
  decide +kernel

theorem ch441790_r2_dead : deadOK 14765201 528900 270600 Fu2.DW Fu2.nD = true := by
  decide +kernel

theorem ch441790_r2_iw : iwOK 14765201 528900 270600 Fu2.IW Fu2.nI = true := by
  decide +kernel

theorem ch441790_r2_xt : xtOK 14765201 528900 270600 Fu2.XT = true := by
  decide +kernel

theorem ch441790_r2_ts : treeSOK 14765201 528900 270600 Fu2.XT Fu2.GS Fu2.TS = true := by
  decide +kernel

theorem ch441790_r2_tk : treesKOK 14765201 528900 270600 Fu2.XT Fu2.GK Fu2.RK Fu2.TK = true := by
  decide +kernel

theorem ch441790_r2_leaves0 : allN 4 (fun i => leafK 14765201 528900 270600 Fu2.FR Fu2.XT Fu2.DW
    Fu2.nD Fu2.IW Fu2.nI Fu2.U Fu2.RK Fu2.LD (Nat.add 0 i)) = true := by
  decide +kernel

theorem ch441790_r2_leaves4 : allN 4 (fun i => leafK 14765201 528900 270600 Fu2.FR Fu2.XT Fu2.DW
    Fu2.nD Fu2.IW Fu2.nI Fu2.U Fu2.RK Fu2.LD (Nat.add 4 i)) = true := by
  decide +kernel

theorem ch441790_r2_leaves8 : allN 4 (fun i => leafK 14765201 528900 270600 Fu2.FR Fu2.XT Fu2.DW
    Fu2.nD Fu2.IW Fu2.nI Fu2.U Fu2.RK Fu2.LD (Nat.add 8 i)) = true := by
  decide +kernel

theorem ch441790_r2_leaves12 : allN 4 (fun i => leafK 14765201 528900 270600 Fu2.FR Fu2.XT Fu2.DW
    Fu2.nD Fu2.IW Fu2.nI Fu2.U Fu2.RK Fu2.LD (Nat.add 12 i)) = true := by
  decide +kernel

end CFSG.KC.FzUT.R2
