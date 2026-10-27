module

public import Certificates.Kernel.P0Vis.Tab
public import Certificates.Kernel.P0Orb.Tab
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000

public section

namespace CFSG.KD.P0Vis

open CFSG.KC.P0Orb CFSG.KC.P0Vis CFSG.KD.P0Orb

#kc_each CFSG.KD.P0Vis bt812462t (fun t => btOK BT BG t) 0 10

theorem bt0 : bt0OK BT BG = true := by decide +kernel

#kc_each CFSG.KD.P0Vis fa812462o (fun o => faOK FA AT RT o) 0 68

#kc_each CFSG.KD.P0Vis fb812462z (fun z => fbOK FB BT z) 0 32

theorem yc : ycOK YE NY YC = true := by decide +kernel

theorem yg : ygOK YE FB NY YG = true := by decide +kernel

theorem lamB : lamBOK BT = true := by decide +kernel

theorem lamS : lamSpan = true := by decide +kernel

theorem nums : (Nat.beq NY 374 && Nat.beq NF 354 && Nat.blt FK (2 ^ (32 * NF)) &&
    Nat.blt FC (2 ^ (16 * NF)) && Nat.blt FA (2 ^ (1024 * 68)) && Nat.blt FB (2 ^ (1024 * 32)) &&
    Nat.blt YE (2 ^ (32 * NY))) = true := by decide +kernel

end CFSG.KD.P0Vis

end
