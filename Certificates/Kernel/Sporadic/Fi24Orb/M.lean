module

public import Certificates.Kernel.Sporadic.Fi24Orb.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.Fi24Orb

open CFSG.KC.Fi24Fix CFSG.KC.Fi24Orb

theorem seg1_26 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB
    (segW W1 (nat_lit 26) (nat_lit 8)) R) (MX (nat_lit 0)) = true := by quickRfl
theorem seg1_18 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB
    (segW W1 (nat_lit 18) (nat_lit 8)) (MX (nat_lit 0))) (MX (nat_lit 1)) = true := by quickRfl
theorem seg1_10 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB
    (segW W1 (nat_lit 10) (nat_lit 8)) (MX (nat_lit 1))) (MX (nat_lit 2)) = true := by quickRfl
theorem seg1_2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB
    (segW W1 (nat_lit 2) (nat_lit 8)) (MX (nat_lit 2))) (MX (nat_lit 3)) = true := by quickRfl
theorem seg1_0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB
    (segW W1 (nat_lit 0) (nat_lit 2)) (MX (nat_lit 3))) (MX (nat_lit 4)) = true := by quickRfl
theorem seg2_34 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB
    (segW W2 (nat_lit 34) (nat_lit 8)) R) (MX (nat_lit 5)) = true := by quickRfl
theorem seg2_26 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB
    (segW W2 (nat_lit 26) (nat_lit 8)) (MX (nat_lit 5))) (MX (nat_lit 6)) = true := by quickRfl
theorem seg2_18 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB
    (segW W2 (nat_lit 18) (nat_lit 8)) (MX (nat_lit 6))) (MX (nat_lit 7)) = true := by quickRfl
theorem seg2_10 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB
    (segW W2 (nat_lit 10) (nat_lit 8)) (MX (nat_lit 7))) (MX (nat_lit 8)) = true := by quickRfl
theorem seg2_2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB
    (segW W2 (nat_lit 2) (nat_lit 8)) (MX (nat_lit 8))) (MX (nat_lit 9)) = true := by quickRfl
theorem seg2_0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB
    (segW W2 (nat_lit 0) (nat_lit 2)) (MX (nat_lit 9))) (MX (nat_lit 10)) = true := by quickRfl

theorem fixR1 : Nat.beq (CFSG.KD.BrFi24.MUL R (MX (nat_lit 4))) (MX (nat_lit 4)) = true := by
  quickRfl
theorem agree1 : agreeOK (MX (nat_lit 4)) (RS (nat_lit 0)) = true := by quickRfl
theorem fixR2 : Nat.beq (CFSG.KD.BrFi24.MUL R (MX (nat_lit 10))) (MX (nat_lit 10)) = true := by
  quickRfl
theorem agree2 : agreeOK (MX (nat_lit 10)) (RS (nat_lit 1)) = true := by quickRfl

end CFSG.KD.Fi24Orb

end
