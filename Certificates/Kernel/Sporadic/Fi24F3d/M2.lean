module

public import Certificates.Kernel.Sporadic.Fi24F3d.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public noncomputable section

namespace CFSG.KD.Fi24F3d

open CFSG.KC.Fi24Fix CFSG.KD.Fi24G2e

theorem M2.n2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG (N2.reverse ++ WEF ++ N2) CFSG.KD.BrFi24.ONE)
    (wordMul CFSG.KD.BrFi24.MUL LG (WE ++ WF ++ WF) CFSG.KD.BrFi24.ONE) = true := by quickRfl

theorem M2.n3 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG (N3.reverse ++ WEF ++ N3) CFSG.KD.BrFi24.ONE)
    (wordMul CFSG.KD.BrFi24.MUL LG (WE ++ WF ++ WF ++ WF) CFSG.KD.BrFi24.ONE) = true := by quickRfl

theorem M2.n4 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG (N4.reverse ++ WEF ++ N4) CFSG.KD.BrFi24.ONE)
    (wordMul CFSG.KD.BrFi24.MUL LG (WE ++ WF ++ WF ++ WF ++ WF) CFSG.KD.BrFi24.ONE) = true := by
  quickRfl

end CFSG.KD.Fi24F3d

end
