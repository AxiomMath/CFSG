module

public import Certificates.Kernel.Sporadic.Fi24G2e.OData
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public noncomputable section

namespace CFSG.KD.Fi24G2e.OW

open CFSG.KD.Fi24G2e CFSG.KD.BrFi24 CFSG.KC.Fi24FixK CFSG.KC.Fi24Fix

theorem p2 : Nat.beq (walk CFSG.KD.Fi24Fix.TG OQ2 37886) 22978 = true := by quickRfl

theorem m2 : Nat.beq (wordMul MUL LG OQ2 ONE) MQ2 = true := by quickRfl

theorem c2 : Nat.beq (MUL (LG 0) MQ2) (MUL MQ2 (LG 2)) = true := by quickRfl

theorem p4 : Nat.beq (walk CFSG.KD.Fi24Fix.TG OQ4 37886) 22975 = true := by quickRfl

theorem m4 : Nat.beq (wordMul MUL LG OQ4 ONE) MQ4 = true := by quickRfl

theorem c4 : Nat.beq (MUL (LG 0) MQ4) (MUL MQ4 (LG 4)) = true := by quickRfl

theorem p6 : Nat.beq (walk CFSG.KD.Fi24Fix.TG OQ6 37886) 22973 = true := by quickRfl

theorem m6 : Nat.beq (wordMul MUL LG OQ6 ONE) MQ6 = true := by quickRfl

theorem c6 : Nat.beq (MUL (LG 0) MQ6) (MUL MQ6 (LG 6)) = true := by quickRfl

end CFSG.KD.Fi24G2e.OW

end
