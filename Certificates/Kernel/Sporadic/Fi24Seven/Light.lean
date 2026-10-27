module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Fi24Seven.Data
public import Certificates.Data.Kernel.Spor.SlpPlan

public section

set_option maxRecDepth 400000

namespace CFSG.KD.F24S

open CFSG.KC.SlpM

theorem plan_ok : planOK nK nR nBase lyK pcR pnR inK ouK = true := by quickRfl

theorem plan1_ok : planOK nK1 nR1 nBase lyK pcR pnR inK ouK = true := by quickRfl

theorem b2_ok : Nat.beq (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB 24) (CFSG.KD.BrFi24.RB 24)) (R 0) = true := by
  quickRfl

theorem len7 : Nat.beq (lenL W7) 1087 = true := by quickRfl

theorem lenE7 : Nat.beq (lenL E7) 119 = true := by quickRfl

theorem lenEK : Nat.beq (lenL EK) 2733 = true := by quickRfl

theorem lenC7 : Nat.beq (lenL C7) 343 = true := by quickRfl

theorem slp7 : slpC (appL W7 E7) 0 = true := by quickRfl

theorem slpK : slpC (appL W7 EK) 0 = true := by quickRfl

@[expose] noncomputable def eqs7 : List (List Nat × List Nat) :=
  [([2412], [6]), ([2414], [8]), ([2176, 140], [140, 2176]), ([2178, 140], [140, 2178]),
    ([2170, 138], [138, 2170]), ([2172, 138], [138, 2172]), ([2174, 138], [138, 2174]),
    ([2416, 2416, 2416, 2416], [])]

theorem eqs7_ok : allL eqs7 (hasEq lyK eqK nK1 1) = true := by quickRfl

theorem nes7_ok : hasEq lyK neK nK1 1 ([2416, 2416], []) = true := by quickRfl

end CFSG.KD.F24S

end
