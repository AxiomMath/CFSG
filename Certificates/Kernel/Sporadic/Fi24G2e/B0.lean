module

public import Certificates.Kernel.Sporadic.Fi24G2e.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public noncomputable section

namespace CFSG.KD.Fi24G2e.B0

open CFSG.KD.Fi24G2e

theorem sq : Nat.beq (CFSG.KD.BrFi24.MUL (BX 0) (BX 0)) CFSG.KD.BrFi24.ONE = true := by quickRfl

theorem tq : Nat.beq (CFSG.KD.BrFi24.MUL (BX 0) CFSG.KD.Fi24Fix.Q) (BX 13) = true := by quickRfl

theorem kq : Nat.beq (CFSG.KD.BrFi24.MUL CFSG.KD.Fi24Fix.Q (BX 13)) (BX 13) = true := by quickRfl

theorem lk : Nat.beq (CFSG.KD.BrFi24.MUL (BX 0) (BX 12))
    (CFSG.KD.BrFi24.MUL (BX 12) CFSG.KD.Fi24Ext.T) = true := by
  quickRfl

end CFSG.KD.Fi24G2e.B0

end
