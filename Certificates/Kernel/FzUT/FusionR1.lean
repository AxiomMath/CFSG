module

public import Certificates.Data.Kernel.FzUT.FusionP
public import Certificates.Kernel.FzUT.FusionD12

public section

namespace CFSG.KC.FzUT.R1

open CFSG.KD

theorem ch441790_r1_forest : forestOK 14765201 528900 1081410 Fu1.FR = true := by
  decide +kernel

theorem ch441790_r1_dead : deadOK 14765201 528900 1081410 Fu1.DW Fu1.nD = true := by
  decide +kernel

theorem ch441790_r1_iw : iwOK 14765201 528900 1081410 Fu1.IW Fu1.nI = true := by
  decide +kernel

theorem ch441790_r1_xt : xtOK 14765201 528900 1081410 Fu1.XT = true := by
  decide +kernel

theorem ch441790_r1_ts : treeSOK 14765201 528900 1081410 Fu1.XT Fu1.GS Fu1.TS = true := by
  decide +kernel

theorem ch441790_r1_tk : treesKOK 14765201 528900 1081410 Fu1.XT Fu1.GK Fu1.RK Fu1.TK = true := by
  decide +kernel

theorem ch441790_r1_leaves0 : allN 4 (fun i => leafK 14765201 528900 1081410 Fu1.FR Fu1.XT Fu1.DW
    Fu1.nD Fu1.IW Fu1.nI Fu1.U Fu1.RK Fu1.LD (Nat.add 0 i)) = true := by
  decide +kernel

theorem ch441790_r1_leaves4 : allN 4 (fun i => leafK 14765201 528900 1081410 Fu1.FR Fu1.XT Fu1.DW
    Fu1.nD Fu1.IW Fu1.nI Fu1.U Fu1.RK Fu1.LD (Nat.add 4 i)) = true := by
  decide +kernel

theorem ch441790_r1_leaves8 : allN 4 (fun i => leafK 14765201 528900 1081410 Fu1.FR Fu1.XT Fu1.DW
    Fu1.nD Fu1.IW Fu1.nI Fu1.U Fu1.RK Fu1.LD (Nat.add 8 i)) = true := by
  decide +kernel

theorem ch441790_r1_leaves12 : allN 4 (fun i => leafK 14765201 528900 1081410 Fu1.FR Fu1.XT Fu1.DW
    Fu1.nD Fu1.IW Fu1.nI Fu1.U Fu1.RK Fu1.LD (Nat.add 12 i)) = true := by
  decide +kernel

end CFSG.KC.FzUT.R1
