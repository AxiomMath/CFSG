module

public import Certificates.Data.Kernel.P0VisLen
public import Certificates.Kernel.P0Vis.Rows
public import CFSG.Monster.B.TwoA.Sp8.P0RankInputs

public section

namespace CFSG.KD.P0Vis

open CFSG.KC.P0Vis CFSG.Monster.B.TwoA.Sp8.WordRel

theorem glen812462_0 : glenOK CFSG.KD.P0VisR0.rows = true := by decide +kernel

theorem glen812462_1 : glenOK CFSG.KD.P0VisR1.rows = true := by decide +kernel

theorem glen812462_2 : glenOK CFSG.KD.P0VisR2.rows = true := by decide +kernel

theorem glen812462_3 : glenOK CFSG.KD.P0VisR3.rows = true := by decide +kernel

theorem fval0 : fval p0Data 0 = 0 := by decide +kernel

theorem vlens : (Nat.beq CFSG.KD.P0VisR0.rows.length 1200 &&
    Nat.beq CFSG.KD.P0VisR1.rows.length 1200 && Nat.beq CFSG.KD.P0VisR2.rows.length 1200 &&
    Nat.beq CFSG.KD.P0VisR3.rows.length 1287) = true := by decide +kernel

theorem glenNeg : glenOK [([], [(List.range 17, [])])] = false := by decide +kernel

end CFSG.KD.P0Vis

end
