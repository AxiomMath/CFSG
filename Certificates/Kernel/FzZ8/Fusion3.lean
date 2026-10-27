module

public import Certificates.Data.Kernel.FzZ8.Z8
public import Certificates.Data.Kernel.FzZ8.Fusion
public import Certificates.Kernel.FzZ8.FusionD

public section

namespace CFSG.KC.FzZ8.R3

open CFSG.KD CFSG.KC.FzUT CFSG.KC.FzZ8

theorem ch441791_r3_forest :
    forestG (emZ 2565 1539 72) (tlZ 2565) rhZ Fz3.FR = true := by
  decide +kernel

theorem ch441791_r3_dead :
    deadG (emZ 2565 1539 72) (tlZ 2565) (wZ 2565) tzZ Fz3.DW Fz3.nD = true := by
  decide +kernel

theorem ch441791_r3_iw : iwG (emZ 2565 1539 72) (tlZ 2565) Fz3.IW Fz3.nI = true := by
  decide +kernel

theorem ch441791_r3_xt : xtG (emZ 2565 1539 72) Fz3.XT = true := by
  decide +kernel

theorem ch441791_r3_ts : treeSG (emZ 2565 1539 72) Fz3.XT Fz3.GS Fz3.TS = true := by
  decide +kernel

theorem ch441791_r3_tk : treesKG (emZ 2565 1539 72) Fz3.XT Fz3.GK Fz3.RK Fz3.TK = true := by
  decide +kernel

theorem ch441791_r3_leaves0 : allN 4 (fun i => leafKG (emZ 2565 1539 72) addZ
    (actZ 2565 1539 72) Fz3.FR Fz3.XT Fz3.DW Fz3.nD Fz3.IW Fz3.nI Fz3.U Fz3.RK Fz3.LD
    (Nat.add 0 i)) = true := by
  decide +kernel

theorem ch441791_r3_leaves4 : allN 4 (fun i => leafKG (emZ 2565 1539 72) addZ
    (actZ 2565 1539 72) Fz3.FR Fz3.XT Fz3.DW Fz3.nD Fz3.IW Fz3.nI Fz3.U Fz3.RK Fz3.LD
    (Nat.add 4 i)) = true := by
  decide +kernel

end CFSG.KC.FzZ8.R3
