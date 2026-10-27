module

public import Certificates.Kernel.Sporadic.Fi24F3d.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public noncomputable section

namespace CFSG.KD.Fi24F3d

open CFSG.KC.Fi24Fix CFSG.KD.Fi24G2e

theorem M0.e5 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG (WE ++ WE ++ WE ++ WE ++ WE) CFSG.KD.BrFi24.ONE)
    CFSG.KD.BrFi24.ONE = true := by quickRfl

theorem M0.ef : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG (WE ++ WF) CFSG.KD.BrFi24.ONE)
    (wordMul CFSG.KD.BrFi24.MUL LG (WF ++ WE) CFSG.KD.BrFi24.ONE) = true := by quickRfl

theorem M0.ey : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG (WE ++ WY) CFSG.KD.BrFi24.ONE)
    (wordMul CFSG.KD.BrFi24.MUL LG (WY ++ WE) CFSG.KD.BrFi24.ONE) = true := by quickRfl

end CFSG.KD.Fi24F3d

end
