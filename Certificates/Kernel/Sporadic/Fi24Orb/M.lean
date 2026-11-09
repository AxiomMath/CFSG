module

public import Certificates.Kernel.Sporadic.Fi24Orb.Data
import Certificates.Kernel.Sporadic.Fi24Fix.Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree CFSG.KD.Fi24Orb MSP "Certificates/Kernel/Sporadic/Fi24Orb/data/msplit.bin" 152491 4 4117257 12454067658395101435

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.Fi24Orb

open CFSG.KC.Fi24Fix CFSG.KC.Fi24Orb

theorem seg1_26_p3 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [24, 24]
    R) (MSP (nat_lit 0)) = true := by quickRfl
theorem seg1_26_p2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [24, 23]
    (MSP (nat_lit 0))) (MSP (nat_lit 1)) = true := by quickRfl
theorem seg1_26_p1 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [23, 24]
    (MSP (nat_lit 1))) (MSP (nat_lit 2)) = true := by quickRfl
theorem seg1_26_p0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [24, 24]
    (MSP (nat_lit 2))) (MX (nat_lit 0)) = true := by quickRfl
theorem seg1_26 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB
    (segW W1 (nat_lit 26) (nat_lit 8)) R) (MX (nat_lit 0)) = true :=
  beq_wordMul_of_eq (w' := [24, 24] ++ ([23, 24] ++ ([24, 23] ++ [24, 24]))) rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append seg1_26_p3 seg1_26_p2)
      seg1_26_p1) seg1_26_p0)

theorem seg1_18_p3 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [24, 23]
    (MX (nat_lit 0))) (MSP (nat_lit 3)) = true := by quickRfl
theorem seg1_18_p2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [24, 23]
    (MSP (nat_lit 3))) (MSP (nat_lit 4)) = true := by quickRfl
theorem seg1_18_p1 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [24, 23]
    (MSP (nat_lit 4))) (MSP (nat_lit 5)) = true := by quickRfl
theorem seg1_18_p0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [24, 23]
    (MSP (nat_lit 5))) (MX (nat_lit 1)) = true := by quickRfl
theorem seg1_18 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB
    (segW W1 (nat_lit 18) (nat_lit 8)) (MX (nat_lit 0))) (MX (nat_lit 1)) = true :=
  beq_wordMul_of_eq (w' := [24, 23] ++ ([24, 23] ++ ([24, 23] ++ [24, 23]))) rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append seg1_18_p3 seg1_18_p2)
      seg1_18_p1) seg1_18_p0)

theorem seg1_10_p3 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [24, 23]
    (MX (nat_lit 1))) (MSP (nat_lit 6)) = true := by quickRfl
theorem seg1_10_p2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [23, 24]
    (MSP (nat_lit 6))) (MSP (nat_lit 7)) = true := by quickRfl
theorem seg1_10_p1 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [24, 24]
    (MSP (nat_lit 7))) (MSP (nat_lit 8)) = true := by quickRfl
theorem seg1_10_p0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [24, 23]
    (MSP (nat_lit 8))) (MX (nat_lit 2)) = true := by quickRfl
theorem seg1_10 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB
    (segW W1 (nat_lit 10) (nat_lit 8)) (MX (nat_lit 1))) (MX (nat_lit 2)) = true :=
  beq_wordMul_of_eq (w' := [24, 23] ++ ([24, 24] ++ ([23, 24] ++ [24, 23]))) rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append seg1_10_p3 seg1_10_p2)
      seg1_10_p1) seg1_10_p0)

theorem seg1_2_p3 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [23, 24]
    (MX (nat_lit 2))) (MSP (nat_lit 9)) = true := by quickRfl
theorem seg1_2_p2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [24, 24]
    (MSP (nat_lit 9))) (MSP (nat_lit 10)) = true := by quickRfl
theorem seg1_2_p1 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [24, 23]
    (MSP (nat_lit 10))) (MSP (nat_lit 11)) = true := by quickRfl
theorem seg1_2_p0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [24, 23]
    (MSP (nat_lit 11))) (MX (nat_lit 3)) = true := by quickRfl
theorem seg1_2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB
    (segW W1 (nat_lit 2) (nat_lit 8)) (MX (nat_lit 2))) (MX (nat_lit 3)) = true :=
  beq_wordMul_of_eq (w' := [24, 23] ++ ([24, 23] ++ ([24, 24] ++ [23, 24]))) rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append seg1_2_p3 seg1_2_p2)
      seg1_2_p1) seg1_2_p0)

theorem seg1_0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB
    (segW W1 (nat_lit 0) (nat_lit 2)) (MX (nat_lit 3))) (MX (nat_lit 4)) = true := by quickRfl

theorem seg2_34_p3 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [23, 24]
    R) (MSP (nat_lit 12)) = true := by quickRfl
theorem seg2_34_p2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [23, 24]
    (MSP (nat_lit 12))) (MSP (nat_lit 13)) = true := by quickRfl
theorem seg2_34_p1 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [23, 24]
    (MSP (nat_lit 13))) (MSP (nat_lit 14)) = true := by quickRfl
theorem seg2_34_p0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [23, 24]
    (MSP (nat_lit 14))) (MX (nat_lit 5)) = true := by quickRfl
theorem seg2_34 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB
    (segW W2 (nat_lit 34) (nat_lit 8)) R) (MX (nat_lit 5)) = true :=
  beq_wordMul_of_eq (w' := [23, 24] ++ ([23, 24] ++ ([23, 24] ++ [23, 24]))) rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append seg2_34_p3 seg2_34_p2)
      seg2_34_p1) seg2_34_p0)

theorem seg2_26_p3 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [23, 24]
    (MX (nat_lit 5))) (MSP (nat_lit 15)) = true := by quickRfl
theorem seg2_26_p2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [23, 24]
    (MSP (nat_lit 15))) (MSP (nat_lit 16)) = true := by quickRfl
theorem seg2_26_p1 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [23, 24]
    (MSP (nat_lit 16))) (MSP (nat_lit 17)) = true := by quickRfl
theorem seg2_26_p0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [23, 24]
    (MSP (nat_lit 17))) (MX (nat_lit 6)) = true := by quickRfl
theorem seg2_26 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB
    (segW W2 (nat_lit 26) (nat_lit 8)) (MX (nat_lit 5))) (MX (nat_lit 6)) = true :=
  beq_wordMul_of_eq (w' := [23, 24] ++ ([23, 24] ++ ([23, 24] ++ [23, 24]))) rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append seg2_26_p3 seg2_26_p2)
      seg2_26_p1) seg2_26_p0)

theorem seg2_18_p3 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [24, 24]
    (MX (nat_lit 6))) (MSP (nat_lit 18)) = true := by quickRfl
theorem seg2_18_p2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [24, 23]
    (MSP (nat_lit 18))) (MSP (nat_lit 19)) = true := by quickRfl
theorem seg2_18_p1 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [24, 23]
    (MSP (nat_lit 19))) (MSP (nat_lit 20)) = true := by quickRfl
theorem seg2_18_p0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [24, 23]
    (MSP (nat_lit 20))) (MX (nat_lit 7)) = true := by quickRfl
theorem seg2_18 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB
    (segW W2 (nat_lit 18) (nat_lit 8)) (MX (nat_lit 6))) (MX (nat_lit 7)) = true :=
  beq_wordMul_of_eq (w' := [24, 23] ++ ([24, 23] ++ ([24, 23] ++ [24, 24]))) rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append seg2_18_p3 seg2_18_p2)
      seg2_18_p1) seg2_18_p0)

theorem seg2_10_p3 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [23, 24]
    (MX (nat_lit 7))) (MSP (nat_lit 21)) = true := by quickRfl
theorem seg2_10_p2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [24, 24]
    (MSP (nat_lit 21))) (MSP (nat_lit 22)) = true := by quickRfl
theorem seg2_10_p1 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [24, 23]
    (MSP (nat_lit 22))) (MSP (nat_lit 23)) = true := by quickRfl
theorem seg2_10_p0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [23, 24]
    (MSP (nat_lit 23))) (MX (nat_lit 8)) = true := by quickRfl
theorem seg2_10 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB
    (segW W2 (nat_lit 10) (nat_lit 8)) (MX (nat_lit 7))) (MX (nat_lit 8)) = true :=
  beq_wordMul_of_eq (w' := [23, 24] ++ ([24, 23] ++ ([24, 24] ++ [23, 24]))) rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append seg2_10_p3 seg2_10_p2)
      seg2_10_p1) seg2_10_p0)

theorem seg2_2_p3 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [24, 24]
    (MX (nat_lit 8))) (MSP (nat_lit 24)) = true := by quickRfl
theorem seg2_2_p2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [24, 23]
    (MSP (nat_lit 24))) (MSP (nat_lit 25)) = true := by quickRfl
theorem seg2_2_p1 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [24, 23]
    (MSP (nat_lit 25))) (MSP (nat_lit 26)) = true := by quickRfl
theorem seg2_2_p0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [24, 23]
    (MSP (nat_lit 26))) (MX (nat_lit 9)) = true := by quickRfl
theorem seg2_2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB
    (segW W2 (nat_lit 2) (nat_lit 8)) (MX (nat_lit 8))) (MX (nat_lit 9)) = true :=
  beq_wordMul_of_eq (w' := [24, 23] ++ ([24, 23] ++ ([24, 23] ++ [24, 24]))) rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append seg2_2_p3 seg2_2_p2)
      seg2_2_p1) seg2_2_p0)

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
