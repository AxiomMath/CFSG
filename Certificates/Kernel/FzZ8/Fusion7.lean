module

public import Certificates.Data.Kernel.FzZ8.Z8
public import Certificates.Data.Kernel.FzZ8.Fusion
public import Certificates.Kernel.FzZ8.FusionD

public section

namespace CFSG.KC.FzZ8.R7

open CFSG.KD CFSG.KC.FzUT CFSG.KC.FzZ8

theorem ch441791_r7_forest :
    forestG (emZ 2565 3591 72) (tlZ 2565) rhZ Fz7.FR = true := by
  decide +kernel

theorem ch441791_r7_dead :
    deadG (emZ 2565 3591 72) (tlZ 2565) (wZ 2565) tzZ Fz7.DW Fz7.nD = true := by
  decide +kernel

theorem ch441791_r7_iw : iwG (emZ 2565 3591 72) (tlZ 2565) Fz7.IW Fz7.nI = true := by
  decide +kernel

theorem ch441791_r7_xt : xtG (emZ 2565 3591 72) Fz7.XT = true := by
  decide +kernel

theorem ch441791_r7_ts : treeSG (emZ 2565 3591 72) Fz7.XT Fz7.GS Fz7.TS = true := by
  decide +kernel

theorem ch441791_r7_tk : treesKG (emZ 2565 3591 72) Fz7.XT Fz7.GK Fz7.RK Fz7.TK = true := by
  decide +kernel

theorem ch441791_r7_leaves0 : allN 4 (fun i => leafKG (emZ 2565 3591 72) addZ
    (actZ 2565 3591 72) Fz7.FR Fz7.XT Fz7.DW Fz7.nD Fz7.IW Fz7.nI Fz7.U Fz7.RK Fz7.LD
    (Nat.add 0 i)) = true := by
  decide +kernel

theorem ch441791_r7_leaves4 : allN 4 (fun i => leafKG (emZ 2565 3591 72) addZ
    (actZ 2565 3591 72) Fz7.FR Fz7.XT Fz7.DW Fz7.nD Fz7.IW Fz7.nI Fz7.U Fz7.RK Fz7.LD
    (Nat.add 4 i)) = true := by
  decide +kernel

end CFSG.KC.FzZ8.R7
