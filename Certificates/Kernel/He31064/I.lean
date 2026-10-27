module

public import Certificates.Kernel.He31064.M
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.He31064.CI

open CFSG.KC.DcTup CFSG.KD.He31064

theorem lens : Nat.beq (lenK reps) 133 && Nat.beq (lenK ri) 133 && Nat.beq (lenK hs) 133 &&
    Nat.beq (lenK IV) 133 && Nat.beq (lenK xp) 251 && Nat.beq (lenK xn) 251 &&
    Nat.beq (lenK lv) 6 && Nat.beq (lenK lvw) 6 && Nat.beq (lenK rg) 2 && Nat.beq (lenK rgi) 2 &&
    Nat.beq (lenK rgw) 2 && Nat.beq (lenK ab) 4 &&
    allL (fun j => Nat.blt j 251) ri && allL (fun e => Nat.blt e.2 252) xp &&
    allL (fun e => Nat.blt e.1 4) xp &&
    allL (fun w => allL (fun l => Nat.blt l 4) w) reps &&
    allL (fun w => allL (fun l => Nat.blt l 4) w) rgw &&
    allL (fun w => allL (fun l => Nat.blt l 2) w) lvw &&
    allN 133 (fun j => Nat.blt 0 (H j)) = true := by quickRfl
theorem i0 : iOK 0 32 = true := by quickRfl
theorem i1 : iOK 32 32 = true := by quickRfl
theorem i2 : iOK 64 32 = true := by quickRfl
theorem i3 : iOK 96 37 = true := by quickRfl
theorem dist : distK 133 IV pairs = true := by quickRfl
theorem edgesC : allL (edgeOK 133 B rg rgi ab X W) edges = true := by quickRfl
theorem inT : inTreeK 133 0 edges inEdge dIn = true := by quickRfl
theorem outT : (outTreeK 0 reach edges outEdge dOut && allNeK reach &&
    allL (fun j => Nat.blt j 133) reach) = true := by quickRfl
theorem mass : (Nat.blt 4030387200 (Nat.mul 2 (massK 6174 H reach)) &&
    Nat.ble 4030387200 (Nat.add massAll 6174)) = true := by quickRfl

end CFSG.KD.He31064.CI

end
