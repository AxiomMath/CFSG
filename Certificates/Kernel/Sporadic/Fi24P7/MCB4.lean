module

public import Certificates.Kernel.Sporadic.Fi24P7.Seg
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatVal

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public noncomputable section

namespace CFSG.KD.Fi24P7

open CFSG.KC.Fi24Fix

#kc_natval CB4.v0_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 8] (MX (nat_lit 22))

theorem CB4.c0_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 8] (MX (nat_lit 22))) CB4.v0_6 = true := by
  quickRfl

#kc_natval CB4.v0_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3] CB4.v0_6

theorem CB4.c0_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3] CB4.v0_6) CB4.v0_5 = true := by
  quickRfl

#kc_natval CB4.v0_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 2, nat_lit 5] CB4.v0_5

theorem CB4.c0_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 2, nat_lit 5] CB4.v0_5) CB4.v0_4 = true := by
  quickRfl

#kc_natval CB4.v0_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 4, nat_lit 3] CB4.v0_4

theorem CB4.c0_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 4, nat_lit 3] CB4.v0_4) CB4.v0_3 = true := by
  quickRfl

#kc_natval CB4.v0_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 1, nat_lit 3] CB4.v0_3

theorem CB4.c0_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 1, nat_lit 3] CB4.v0_3) CB4.v0_2 = true := by
  quickRfl

theorem CB4.c0_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 8, nat_lit 1, nat_lit 7] CB4.v0_2) (MX (nat_lit 21)) = true := by
  quickRfl

theorem CB4.c0 : chB4 (nat_lit 0) = true :=
  chStep_of (P := J.CB4) (b := nat_lit 21) (k := nat_lit 11) (i := nat_lit 0)
    (w := [nat_lit 8, nat_lit 1, nat_lit 7] ++ ([nat_lit 2, nat_lit 1, nat_lit 3] ++ ([nat_lit 2, nat_lit 4, nat_lit 3] ++ ([nat_lit 7, nat_lit 2, nat_lit 5] ++ ([nat_lit 4, nat_lit 3] ++ [nat_lit 7, nat_lit 8])))))
    (Y := (MX (nat_lit 22))) (Z := (MX (nat_lit 21))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CB4.c0_p6 CB4.c0_p5) CB4.c0_p4) CB4.c0_p3) CB4.c0_p2) CB4.c0_p1)

#kc_natval CB4.v1_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 0, nat_lit 1] (MX (nat_lit 23))

theorem CB4.c1_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 0, nat_lit 1] (MX (nat_lit 23))) CB4.v1_6 = true := by
  quickRfl

#kc_natval CB4.v1_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 4] CB4.v1_6

theorem CB4.c1_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 4] CB4.v1_6) CB4.v1_5 = true := by
  quickRfl

#kc_natval CB4.v1_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 7, nat_lit 3] CB4.v1_5

theorem CB4.c1_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 7, nat_lit 3] CB4.v1_5) CB4.v1_4 = true := by
  quickRfl

#kc_natval CB4.v1_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3, nat_lit 2] CB4.v1_4

theorem CB4.c1_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3, nat_lit 2] CB4.v1_4) CB4.v1_3 = true := by
  quickRfl

#kc_natval CB4.v1_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 6, nat_lit 5] CB4.v1_3

theorem CB4.c1_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 6, nat_lit 5] CB4.v1_3) CB4.v1_2 = true := by
  quickRfl

theorem CB4.c1_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 5, nat_lit 5] CB4.v1_2) (MX (nat_lit 22)) = true := by
  quickRfl

theorem CB4.c1 : chB4 (nat_lit 1) = true :=
  chStep_of (P := J.CB4) (b := nat_lit 21) (k := nat_lit 11) (i := nat_lit 1)
    (w := [nat_lit 2, nat_lit 5, nat_lit 5] ++ ([nat_lit 1, nat_lit 6, nat_lit 5] ++ ([nat_lit 4, nat_lit 3, nat_lit 2] ++ ([nat_lit 1, nat_lit 7, nat_lit 3] ++ ([nat_lit 2, nat_lit 4] ++ [nat_lit 0, nat_lit 1])))))
    (Y := (MX (nat_lit 23))) (Z := (MX (nat_lit 22))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CB4.c1_p6 CB4.c1_p5) CB4.c1_p4) CB4.c1_p3) CB4.c1_p2) CB4.c1_p1)

#kc_natval CB4.v2_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2] (MX (nat_lit 24))

theorem CB4.c2_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2] (MX (nat_lit 24))) CB4.v2_6 = true := by
  quickRfl

#kc_natval CB4.v2_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 8, nat_lit 7] CB4.v2_6

theorem CB4.c2_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 8, nat_lit 7] CB4.v2_6) CB4.v2_5 = true := by
  quickRfl

#kc_natval CB4.v2_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3, nat_lit 5] CB4.v2_5

theorem CB4.c2_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3, nat_lit 5] CB4.v2_5) CB4.v2_4 = true := by
  quickRfl

#kc_natval CB4.v2_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2, nat_lit 1] CB4.v2_4

theorem CB4.c2_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2, nat_lit 1] CB4.v2_4) CB4.v2_3 = true := by
  quickRfl

#kc_natval CB4.v2_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 6, nat_lit 7] CB4.v2_3

theorem CB4.c2_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 6, nat_lit 7] CB4.v2_3) CB4.v2_2 = true := by
  quickRfl

theorem CB4.c2_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 3, nat_lit 4] CB4.v2_2) (MX (nat_lit 23)) = true := by
  quickRfl

theorem CB4.c2 : chB4 (nat_lit 2) = true :=
  chStep_of (P := J.CB4) (b := nat_lit 21) (k := nat_lit 11) (i := nat_lit 2)
    (w := [nat_lit 2, nat_lit 3, nat_lit 4] ++ ([nat_lit 5, nat_lit 6, nat_lit 7] ++ ([nat_lit 3, nat_lit 2, nat_lit 1] ++ ([nat_lit 4, nat_lit 3, nat_lit 5] ++ ([nat_lit 8, nat_lit 7] ++ [nat_lit 3, nat_lit 2])))))
    (Y := (MX (nat_lit 24))) (Z := (MX (nat_lit 23))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CB4.c2_p6 CB4.c2_p5) CB4.c2_p4) CB4.c2_p3) CB4.c2_p2) CB4.c2_p1)

#kc_natval CB4.v3_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 5] (MX (nat_lit 25))

theorem CB4.c3_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 5] (MX (nat_lit 25))) CB4.v3_6 = true := by
  quickRfl

#kc_natval CB4.v3_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 3] CB4.v3_6

theorem CB4.c3_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 3] CB4.v3_6) CB4.v3_5 = true := by
  quickRfl

#kc_natval CB4.v3_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2, nat_lit 8] CB4.v3_5

theorem CB4.c3_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2, nat_lit 8] CB4.v3_5) CB4.v3_4 = true := by
  quickRfl

#kc_natval CB4.v3_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 4, nat_lit 7] CB4.v3_4

theorem CB4.c3_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 4, nat_lit 7] CB4.v3_4) CB4.v3_3 = true := by
  quickRfl

#kc_natval CB4.v3_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2, nat_lit 1] CB4.v3_3

theorem CB4.c3_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2, nat_lit 1] CB4.v3_3) CB4.v3_2 = true := by
  quickRfl

theorem CB4.c3_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 0, nat_lit 4] CB4.v3_2) (MX (nat_lit 24)) = true := by
  quickRfl

theorem CB4.c3 : chB4 (nat_lit 3) = true :=
  chStep_of (P := J.CB4) (b := nat_lit 21) (k := nat_lit 11) (i := nat_lit 3)
    (w := [nat_lit 1, nat_lit 0, nat_lit 4] ++ ([nat_lit 3, nat_lit 2, nat_lit 1] ++ ([nat_lit 5, nat_lit 4, nat_lit 7] ++ ([nat_lit 3, nat_lit 2, nat_lit 8] ++ ([nat_lit 7, nat_lit 3] ++ [nat_lit 4, nat_lit 5])))))
    (Y := (MX (nat_lit 25))) (Z := (MX (nat_lit 24))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CB4.c3_p6 CB4.c3_p5) CB4.c3_p4) CB4.c3_p3) CB4.c3_p2) CB4.c3_p1)

#kc_natval CB4.v4_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 3] (MX (nat_lit 26))

theorem CB4.c4_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 3] (MX (nat_lit 26))) CB4.v4_6 = true := by
  quickRfl

#kc_natval CB4.v4_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 1] CB4.v4_6

theorem CB4.c4_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 1] CB4.v4_6) CB4.v4_5 = true := by
  quickRfl

#kc_natval CB4.v4_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7, nat_lit 4] CB4.v4_5

theorem CB4.c4_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7, nat_lit 4] CB4.v4_5) CB4.v4_4 = true := by
  quickRfl

#kc_natval CB4.v4_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 8, nat_lit 2] CB4.v4_4

theorem CB4.c4_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 8, nat_lit 2] CB4.v4_4) CB4.v4_3 = true := by
  quickRfl

#kc_natval CB4.v4_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 4, nat_lit 3] CB4.v4_3

theorem CB4.c4_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 4, nat_lit 3] CB4.v4_3) CB4.v4_2 = true := by
  quickRfl

theorem CB4.c4_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 6, nat_lit 9, nat_lit 6] CB4.v4_2) (MX (nat_lit 25)) = true := by
  quickRfl

theorem CB4.c4 : chB4 (nat_lit 4) = true :=
  chStep_of (P := J.CB4) (b := nat_lit 21) (k := nat_lit 11) (i := nat_lit 4)
    (w := [nat_lit 6, nat_lit 9, nat_lit 6] ++ ([nat_lit 5, nat_lit 4, nat_lit 3] ++ ([nat_lit 7, nat_lit 8, nat_lit 2] ++ ([nat_lit 3, nat_lit 7, nat_lit 4] ++ ([nat_lit 5, nat_lit 1] ++ [nat_lit 2, nat_lit 3])))))
    (Y := (MX (nat_lit 26))) (Z := (MX (nat_lit 25))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CB4.c4_p6 CB4.c4_p5) CB4.c4_p4) CB4.c4_p3) CB4.c4_p2) CB4.c4_p1)

#kc_natval CB4.v5_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 6, nat_lit 5] (MX (nat_lit 27))

theorem CB4.c5_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 6, nat_lit 5] (MX (nat_lit 27))) CB4.v5_6 = true := by
  quickRfl

#kc_natval CB4.v5_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7] CB4.v5_6

theorem CB4.c5_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7] CB4.v5_6) CB4.v5_5 = true := by
  quickRfl

#kc_natval CB4.v5_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 1, nat_lit 2] CB4.v5_5

theorem CB4.c5_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 1, nat_lit 2] CB4.v5_5) CB4.v5_4 = true := by
  quickRfl

#kc_natval CB4.v5_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 8, nat_lit 5, nat_lit 3] CB4.v5_4

theorem CB4.c5_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 8, nat_lit 5, nat_lit 3] CB4.v5_4) CB4.v5_3 = true := by
  quickRfl

#kc_natval CB4.v5_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 3, nat_lit 7] CB4.v5_3

theorem CB4.c5_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 3, nat_lit 7] CB4.v5_3) CB4.v5_2 = true := by
  quickRfl

theorem CB4.c5_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 0, nat_lit 1] CB4.v5_2) (MX (nat_lit 26)) = true := by
  quickRfl

theorem CB4.c5 : chB4 (nat_lit 5) = true :=
  chStep_of (P := J.CB4) (b := nat_lit 21) (k := nat_lit 11) (i := nat_lit 5)
    (w := [nat_lit 4, nat_lit 0, nat_lit 1] ++ ([nat_lit 2, nat_lit 3, nat_lit 7] ++ ([nat_lit 8, nat_lit 5, nat_lit 3] ++ ([nat_lit 4, nat_lit 1, nat_lit 2] ++ ([nat_lit 3, nat_lit 7] ++ [nat_lit 6, nat_lit 5])))))
    (Y := (MX (nat_lit 27))) (Z := (MX (nat_lit 26))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CB4.c5_p6 CB4.c5_p5) CB4.c5_p4) CB4.c5_p3) CB4.c5_p2) CB4.c5_p1)

#kc_natval CB4.v6_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 3] (MX (nat_lit 28))

theorem CB4.c6_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 3] (MX (nat_lit 28))) CB4.v6_6 = true := by
  quickRfl

#kc_natval CB4.v6_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 6] CB4.v6_6

theorem CB4.c6_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 6] CB4.v6_6) CB4.v6_5 = true := by
  quickRfl

#kc_natval CB4.v6_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 3, nat_lit 4] CB4.v6_5

theorem CB4.c6_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 3, nat_lit 4] CB4.v6_5) CB4.v6_4 = true := by
  quickRfl

#kc_natval CB4.v6_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 0, nat_lit 1] CB4.v6_4

theorem CB4.c6_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 0, nat_lit 1] CB4.v6_4) CB4.v6_3 = true := by
  quickRfl

#kc_natval CB4.v6_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 0, nat_lit 6] CB4.v6_3

theorem CB4.c6_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 0, nat_lit 6] CB4.v6_3) CB4.v6_2 = true := by
  quickRfl

theorem CB4.c6_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3, nat_lit 2] CB4.v6_2) (MX (nat_lit 27)) = true := by
  quickRfl

theorem CB4.c6 : chB4 (nat_lit 6) = true :=
  chStep_of (P := J.CB4) (b := nat_lit 21) (k := nat_lit 11) (i := nat_lit 6)
    (w := [nat_lit 4, nat_lit 3, nat_lit 2] ++ ([nat_lit 1, nat_lit 0, nat_lit 6] ++ ([nat_lit 1, nat_lit 0, nat_lit 1] ++ ([nat_lit 2, nat_lit 3, nat_lit 4] ++ ([nat_lit 5, nat_lit 6] ++ [nat_lit 7, nat_lit 3])))))
    (Y := (MX (nat_lit 28))) (Z := (MX (nat_lit 27))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CB4.c6_p6 CB4.c6_p5) CB4.c6_p4) CB4.c6_p3) CB4.c6_p2) CB4.c6_p1)

#kc_natval CB4.v7_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 5] (MX (nat_lit 29))

theorem CB4.c7_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 5] (MX (nat_lit 29))) CB4.v7_6 = true := by
  quickRfl

#kc_natval CB4.v7_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2] CB4.v7_6

theorem CB4.c7_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2] CB4.v7_6) CB4.v7_5 = true := by
  quickRfl

#kc_natval CB4.v7_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 0, nat_lit 4] CB4.v7_5

theorem CB4.c7_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 0, nat_lit 4] CB4.v7_5) CB4.v7_4 = true := by
  quickRfl

#kc_natval CB4.v7_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 3, nat_lit 2] CB4.v7_4

theorem CB4.c7_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 3, nat_lit 2] CB4.v7_4) CB4.v7_3 = true := by
  quickRfl

#kc_natval CB4.v7_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 5, nat_lit 8] CB4.v7_3

theorem CB4.c7_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 5, nat_lit 8] CB4.v7_3) CB4.v7_2 = true := by
  quickRfl

theorem CB4.c7_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 1, nat_lit 4] CB4.v7_2) (MX (nat_lit 28)) = true := by
  quickRfl

theorem CB4.c7 : chB4 (nat_lit 7) = true :=
  chStep_of (P := J.CB4) (b := nat_lit 21) (k := nat_lit 11) (i := nat_lit 7)
    (w := [nat_lit 2, nat_lit 1, nat_lit 4] ++ ([nat_lit 3, nat_lit 5, nat_lit 8] ++ ([nat_lit 7, nat_lit 3, nat_lit 2] ++ ([nat_lit 1, nat_lit 0, nat_lit 4] ++ ([nat_lit 3, nat_lit 2] ++ [nat_lit 1, nat_lit 5])))))
    (Y := (MX (nat_lit 29))) (Z := (MX (nat_lit 28))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CB4.c7_p6 CB4.c7_p5) CB4.c7_p4) CB4.c7_p3) CB4.c7_p2) CB4.c7_p1)

#kc_natval CB4.v8_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7] (MX (nat_lit 30))

theorem CB4.c8_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7] (MX (nat_lit 30))) CB4.v8_6 = true := by
  quickRfl

#kc_natval CB4.v8_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 4] CB4.v8_6

theorem CB4.c8_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 4] CB4.v8_6) CB4.v8_5 = true := by
  quickRfl

#kc_natval CB4.v8_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 6, nat_lit 9, nat_lit 6] CB4.v8_5

theorem CB4.c8_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 6, nat_lit 9, nat_lit 6] CB4.v8_5) CB4.v8_4 = true := by
  quickRfl

#kc_natval CB4.v8_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 4, nat_lit 5] CB4.v8_4

theorem CB4.c8_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 4, nat_lit 5] CB4.v8_4) CB4.v8_3 = true := by
  quickRfl

#kc_natval CB4.v8_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 8, nat_lit 7] CB4.v8_3

theorem CB4.c8_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 8, nat_lit 7] CB4.v8_3) CB4.v8_2 = true := by
  quickRfl

theorem CB4.c8_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 7, nat_lit 3] CB4.v8_2) (MX (nat_lit 29)) = true := by
  quickRfl

theorem CB4.c8 : chB4 (nat_lit 8) = true :=
  chStep_of (P := J.CB4) (b := nat_lit 21) (k := nat_lit 11) (i := nat_lit 8)
    (w := [nat_lit 4, nat_lit 7, nat_lit 3] ++ ([nat_lit 2, nat_lit 8, nat_lit 7] ++ ([nat_lit 3, nat_lit 4, nat_lit 5] ++ ([nat_lit 6, nat_lit 9, nat_lit 6] ++ ([nat_lit 5, nat_lit 4] ++ [nat_lit 3, nat_lit 7])))))
    (Y := (MX (nat_lit 30))) (Z := (MX (nat_lit 29))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CB4.c8_p6 CB4.c8_p5) CB4.c8_p4) CB4.c8_p3) CB4.c8_p2) CB4.c8_p1)

#kc_natval CB4.v9_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 8] (MX (nat_lit 31))

theorem CB4.c9_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 8] (MX (nat_lit 31))) CB4.v9_6 = true := by
  quickRfl

#kc_natval CB4.v9_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 3] CB4.v9_6

theorem CB4.c9_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 3] CB4.v9_6) CB4.v9_5 = true := by
  quickRfl

#kc_natval CB4.v9_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 0, nat_lit 1] CB4.v9_5

theorem CB4.c9_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 0, nat_lit 1] CB4.v9_5) CB4.v9_4 = true := by
  quickRfl

#kc_natval CB4.v9_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 2, nat_lit 3] CB4.v9_4

theorem CB4.c9_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 2, nat_lit 3] CB4.v9_4) CB4.v9_3 = true := by
  quickRfl

#kc_natval CB4.v9_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 4, nat_lit 5] CB4.v9_3

theorem CB4.c9_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 4, nat_lit 5] CB4.v9_3) CB4.v9_2 = true := by
  quickRfl

theorem CB4.c9_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 8, nat_lit 2, nat_lit 3] CB4.v9_2) (MX (nat_lit 30)) = true := by
  quickRfl

theorem CB4.c9 : chB4 (nat_lit 9) = true :=
  chStep_of (P := J.CB4) (b := nat_lit 21) (k := nat_lit 11) (i := nat_lit 9)
    (w := [nat_lit 8, nat_lit 2, nat_lit 3] ++ ([nat_lit 7, nat_lit 4, nat_lit 5] ++ ([nat_lit 1, nat_lit 2, nat_lit 3] ++ ([nat_lit 4, nat_lit 0, nat_lit 1] ++ ([nat_lit 2, nat_lit 3] ++ [nat_lit 7, nat_lit 8])))))
    (Y := (MX (nat_lit 31))) (Z := (MX (nat_lit 30))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CB4.c9_p6 CB4.c9_p5) CB4.c9_p4) CB4.c9_p3) CB4.c9_p2) CB4.c9_p1)

#kc_natval CB4.v10_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 9] CFSG.KD.BrFi24.ONE

theorem CB4.c10_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 9] CFSG.KD.BrFi24.ONE) CB4.v10_6 = true := by
  quickRfl

#kc_natval CB4.v10_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 0] CB4.v10_6

theorem CB4.c10_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 0] CB4.v10_6) CB4.v10_5 = true := by
  quickRfl

#kc_natval CB4.v10_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3, nat_lit 2] CB4.v10_5

theorem CB4.c10_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3, nat_lit 2] CB4.v10_5) CB4.v10_4 = true := by
  quickRfl

#kc_natval CB4.v10_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 6, nat_lit 5] CB4.v10_4

theorem CB4.c10_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 6, nat_lit 5] CB4.v10_4) CB4.v10_3 = true := by
  quickRfl

#kc_natval CB4.v10_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 2, nat_lit 3] CB4.v10_3

theorem CB4.c10_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 2, nat_lit 3] CB4.v10_3) CB4.v10_2 = true := by
  quickRfl

theorem CB4.c10_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 3, nat_lit 4] CB4.v10_2) (MX (nat_lit 31)) = true := by
  quickRfl

theorem CB4.c10 : chB4 (nat_lit 10) = true :=
  chStep_of (P := J.CB4) (b := nat_lit 21) (k := nat_lit 11) (i := nat_lit 10)
    (w := [nat_lit 5, nat_lit 3, nat_lit 4] ++ ([nat_lit 1, nat_lit 2, nat_lit 3] ++ ([nat_lit 7, nat_lit 6, nat_lit 5] ++ ([nat_lit 4, nat_lit 3, nat_lit 2] ++ ([nat_lit 1, nat_lit 0] ++ [nat_lit 7, nat_lit 9])))))
    (Y := CFSG.KD.BrFi24.ONE) (Z := (MX (nat_lit 31))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CB4.c10_p6 CB4.c10_p5) CB4.c10_p4) CB4.c10_p3) CB4.c10_p2) CB4.c10_p1)

end CFSG.KD.Fi24P7

end
