module

public import Certificates.Kernel.Sporadic.Fi24G2e.Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
import Certificates.Kernel.Sporadic.Fi24Fix.Split

#kc_repo #kc_ktree CFSG.KD.Fi24G2e B1S "Certificates/Kernel/Sporadic/Fi24G2e/data/b1s.bin" 152491 4 1524910
  5087707618717838416

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public noncomputable section

namespace CFSG.KD.Fi24G2e.B1

open CFSG.KD.Fi24G2e CFSG.KC.Fi24Fix

theorem p0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB PC5 CFSG.KD.BrFi24.ONE)
    (BX 14) = true := by
  quickRfl

theorem p1_2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [18, 3] (BX 14)) (B1S (nat_lit 0)) = true := by
  quickRfl

theorem p1_1 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [13, 3] (B1S (nat_lit 0))) (B1S (nat_lit 1)) = true := by
  quickRfl

theorem p1_0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [14, 4] (B1S (nat_lit 1))) (BX 15) = true := by
  quickRfl

theorem p1 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB PC4 (BX 14)) (BX 15) = true :=
  beq_wordMul_of_eq (w' := [14, 4] ++ ([13, 3] ++ [18, 3])) rfl
    (beq_wordMul_append (beq_wordMul_append p1_2 p1_1) p1_0)

theorem p2_2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [15, 5] (BX 15)) (B1S (nat_lit 2)) = true := by
  quickRfl

theorem p2_1 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [16, 6] (B1S (nat_lit 2))) (B1S (nat_lit 3)) = true := by
  quickRfl

theorem p2_0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [14, 7] (B1S (nat_lit 3))) (BX 16) = true := by
  quickRfl

theorem p2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB PC3 (BX 15)) (BX 16) = true :=
  beq_wordMul_of_eq (w' := [14, 7] ++ ([16, 6] ++ [15, 5])) rfl
    (beq_wordMul_append (beq_wordMul_append p2_2 p2_1) p2_0)

theorem p3_2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [17, 9] (BX 16)) (B1S (nat_lit 4)) = true := by
  quickRfl

theorem p3_1 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [11, 10] (B1S (nat_lit 4))) (B1S (nat_lit 5)) = true := by
  quickRfl

theorem p3_0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [12, 21] (B1S (nat_lit 5))) (BX 17) = true := by
  quickRfl

theorem p3 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB PC2 (BX 16)) (BX 17) = true :=
  beq_wordMul_of_eq (w' := [12, 21] ++ ([11, 10] ++ [17, 9])) rfl
    (beq_wordMul_append (beq_wordMul_append p3_2 p3_1) p3_0)

theorem p4_2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [14, 2] (BX 17)) (B1S (nat_lit 6)) = true := by
  quickRfl

theorem p4_1 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [16, 4] (B1S (nat_lit 6))) (B1S (nat_lit 7)) = true := by
  quickRfl

theorem p4_0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [14, 7] (B1S (nat_lit 7))) (BX 18) = true := by
  quickRfl

theorem p4 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB PC1 (BX 17)) (BX 18) = true :=
  beq_wordMul_of_eq (w' := [14, 7] ++ ([16, 4] ++ [14, 2])) rfl
    (beq_wordMul_append (beq_wordMul_append p4_2 p4_1) p4_0)

theorem p5_2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [19, 4] (BX 18)) (B1S (nat_lit 8)) = true := by
  quickRfl

theorem p5_1 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [14, 7] (B1S (nat_lit 8))) (B1S (nat_lit 9)) = true := by
  quickRfl

theorem p5_0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB [12, 2] (B1S (nat_lit 9))) (BX 12) = true := by
  quickRfl

theorem p5 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB PC0 (BX 18)) (BX 12) = true :=
  beq_wordMul_of_eq (w' := [12, 2] ++ ([14, 7] ++ [19, 4])) rfl
    (beq_wordMul_append (beq_wordMul_append p5_2 p5_1) p5_0)

end CFSG.KD.Fi24G2e.B1

end
