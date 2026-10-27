module

public import Certificates.Kernel.Sporadic.Fi24F3d.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public noncomputable section

namespace CFSG.KD.Fi24F3d

open CFSG.KC.Fi24Fix CFSG.KD.Fi24G2e

theorem M1.y7 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG (WY ++ WY ++ WY ++ WY ++ WY ++ WY ++ WY)
    CFSG.KD.BrFi24.ONE) CFSG.KD.BrFi24.ONE = true := by quickRfl

theorem M1.sw : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG (NS.reverse ++ WE ++ NS) CFSG.KD.BrFi24.ONE)
    (wordMul CFSG.KD.BrFi24.MUL LG WF CFSG.KD.BrFi24.ONE) = true := by quickRfl

end CFSG.KD.Fi24F3d

end
