module

public import Certificates.Kernel.P0Orb.Tab
public import Certificates.Kernel.P0Orb.Rows
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000

public section

namespace CFSG.KD.P0Orb

open CFSG.KC.P0Orb

#kc_each CFSG.KD.P0Orb at812462t (fun t => atOK AT GC t) 0 10

theorem at0 : at0OK AT GC = true := by decide +kernel

theorem bc : bcOK BC BU beta = true := by decide +kernel

theorem rt : rtOK RT N = true := by decide +kernel

theorem n_eq : N = 4887 := rfl

theorem lens : (Nat.beq P0OrbR0.rows.length 1 && Nat.beq P0OrbR1.rows.length 599 &&
    Nat.beq P0OrbR2.rows.length 600 && Nat.beq P0OrbR3.rows.length 600 &&
    Nat.beq P0OrbR4.rows.length 600 && Nat.beq P0OrbR5.rows.length 600 &&
    Nat.beq P0OrbR6.rows.length 600 && Nat.beq P0OrbR7.rows.length 600 &&
    Nat.beq P0OrbR8.rows.length 687) = true := by decide +kernel

end CFSG.KD.P0Orb

end
