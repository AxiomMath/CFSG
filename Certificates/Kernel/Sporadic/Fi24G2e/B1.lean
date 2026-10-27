module

public import Certificates.Kernel.Sporadic.Fi24G2e.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public noncomputable section

namespace CFSG.KD.Fi24G2e.B1

open CFSG.KD.Fi24G2e CFSG.KC.Fi24Fix

theorem p0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB PC5 CFSG.KD.BrFi24.ONE)
    (BX 14) = true := by
  quickRfl

theorem p1 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB PC4 (BX 14)) (BX 15) = true := by
  quickRfl

theorem p2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB PC3 (BX 15)) (BX 16) = true := by
  quickRfl

theorem p3 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB PC2 (BX 16)) (BX 17) = true := by
  quickRfl

theorem p4 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB PC1 (BX 17)) (BX 18) = true := by
  quickRfl

theorem p5 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB PC0 (BX 18)) (BX 12) = true := by
  quickRfl

end CFSG.KD.Fi24G2e.B1

end
