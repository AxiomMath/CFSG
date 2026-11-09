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

#kc_natval CA2.v0_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 6] (MX (nat_lit 1))

theorem CA2.c0_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 6] (MX (nat_lit 1))) CA2.v0_6 = true := by
  quickRfl

#kc_natval CA2.v0_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 4] CA2.v0_6

theorem CA2.c0_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 4] CA2.v0_6) CA2.v0_5 = true := by
  quickRfl

#kc_natval CA2.v0_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 1, nat_lit 1] CA2.v0_5

theorem CA2.c0_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 1, nat_lit 1] CA2.v0_5) CA2.v0_4 = true := by
  quickRfl

#kc_natval CA2.v0_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 4, nat_lit 2] CA2.v0_4

theorem CA2.c0_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 4, nat_lit 2] CA2.v0_4) CA2.v0_3 = true := by
  quickRfl

#kc_natval CA2.v0_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3, nat_lit 7] CA2.v0_3

theorem CA2.c0_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3, nat_lit 7] CA2.v0_3) CA2.v0_2 = true := by
  quickRfl

theorem CA2.c0_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 3, nat_lit 2] CA2.v0_2) (MX (nat_lit 0)) = true := by
  quickRfl

theorem CA2.c0 : chA2 (nat_lit 0) = true :=
  chStep_of (P := J.CA2) (b := nat_lit 0) (k := nat_lit 10) (i := nat_lit 0)
    (w := [nat_lit 1, nat_lit 3, nat_lit 2] ++ ([nat_lit 4, nat_lit 3, nat_lit 7] ++ ([nat_lit 3, nat_lit 4, nat_lit 2] ++ ([nat_lit 3, nat_lit 1, nat_lit 1] ++ ([nat_lit 3, nat_lit 4] ++ [nat_lit 5, nat_lit 6])))))
    (Y := (MX (nat_lit 1))) (Z := (MX (nat_lit 0))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CA2.c0_p6 CA2.c0_p5) CA2.c0_p4) CA2.c0_p3) CA2.c0_p2) CA2.c0_p1)

#kc_natval CA2.v1_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 6] (MX (nat_lit 2))

theorem CA2.c1_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 6] (MX (nat_lit 2))) CA2.v1_6 = true := by
  quickRfl

#kc_natval CA2.v1_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 4] CA2.v1_6

theorem CA2.c1_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 4] CA2.v1_6) CA2.v1_5 = true := by
  quickRfl

#kc_natval CA2.v1_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 8, nat_lit 7] CA2.v1_5

theorem CA2.c1_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 8, nat_lit 7] CA2.v1_5) CA2.v1_4 = true := by
  quickRfl

#kc_natval CA2.v1_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 7, nat_lit 3] CA2.v1_4

theorem CA2.c1_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 7, nat_lit 3] CA2.v1_4) CA2.v1_3 = true := by
  quickRfl

#kc_natval CA2.v1_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3, nat_lit 5] CA2.v1_3

theorem CA2.c1_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3, nat_lit 5] CA2.v1_3) CA2.v1_2 = true := by
  quickRfl

theorem CA2.c1_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 3, nat_lit 2] CA2.v1_2) (MX (nat_lit 1)) = true := by
  quickRfl

theorem CA2.c1 : chA2 (nat_lit 1) = true :=
  chStep_of (P := J.CA2) (b := nat_lit 0) (k := nat_lit 10) (i := nat_lit 1)
    (w := [nat_lit 7, nat_lit 3, nat_lit 2] ++ ([nat_lit 4, nat_lit 3, nat_lit 5] ++ ([nat_lit 4, nat_lit 7, nat_lit 3] ++ ([nat_lit 2, nat_lit 8, nat_lit 7] ++ ([nat_lit 3, nat_lit 4] ++ [nat_lit 5, nat_lit 6])))))
    (Y := (MX (nat_lit 2))) (Z := (MX (nat_lit 1))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CA2.c1_p6 CA2.c1_p5) CA2.c1_p4) CA2.c1_p3) CA2.c1_p2) CA2.c1_p1)

#kc_natval CA2.v2_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 3] (MX (nat_lit 3))

theorem CA2.c2_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 3] (MX (nat_lit 3))) CA2.v2_6 = true := by
  quickRfl

#kc_natval CA2.v2_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 4] CA2.v2_6

theorem CA2.c2_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 4] CA2.v2_6) CA2.v2_5 = true := by
  quickRfl

#kc_natval CA2.v2_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 4, nat_lit 5] CA2.v2_5

theorem CA2.c2_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 4, nat_lit 5] CA2.v2_5) CA2.v2_4 = true := by
  quickRfl

#kc_natval CA2.v2_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 8, nat_lit 2, nat_lit 3] CA2.v2_4

theorem CA2.c2_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 8, nat_lit 2, nat_lit 3] CA2.v2_4) CA2.v2_3 = true := by
  quickRfl

#kc_natval CA2.v2_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3, nat_lit 7] CA2.v2_3

theorem CA2.c2_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3, nat_lit 7] CA2.v2_3) CA2.v2_2 = true := by
  quickRfl

theorem CA2.c2_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 9, nat_lit 6, nat_lit 5] CA2.v2_2) (MX (nat_lit 2)) = true := by
  quickRfl

theorem CA2.c2 : chA2 (nat_lit 2) = true :=
  chStep_of (P := J.CA2) (b := nat_lit 0) (k := nat_lit 10) (i := nat_lit 2)
    (w := [nat_lit 9, nat_lit 6, nat_lit 5] ++ ([nat_lit 4, nat_lit 3, nat_lit 7] ++ ([nat_lit 8, nat_lit 2, nat_lit 3] ++ ([nat_lit 7, nat_lit 4, nat_lit 5] ++ ([nat_lit 3, nat_lit 4] ++ [nat_lit 2, nat_lit 3])))))
    (Y := (MX (nat_lit 3))) (Z := (MX (nat_lit 2))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CA2.c2_p6 CA2.c2_p5) CA2.c2_p4) CA2.c2_p3) CA2.c2_p2) CA2.c2_p1)

#kc_natval CA2.v3_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 2] (MX (nat_lit 4))

theorem CA2.c3_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 2] (MX (nat_lit 4))) CA2.v3_6 = true := by
  quickRfl

#kc_natval CA2.v3_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 3] CA2.v3_6

theorem CA2.c3_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 3] CA2.v3_6) CA2.v3_5 = true := by
  quickRfl

#kc_natval CA2.v3_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7, nat_lit 8] CA2.v3_5

theorem CA2.c3_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7, nat_lit 8] CA2.v3_5) CA2.v3_4 = true := by
  quickRfl

#kc_natval CA2.v3_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 2, nat_lit 4] CA2.v3_4

theorem CA2.c3_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 2, nat_lit 4] CA2.v3_4) CA2.v3_3 = true := by
  quickRfl

#kc_natval CA2.v3_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3, nat_lit 1] CA2.v3_3

theorem CA2.c3_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3, nat_lit 1] CA2.v3_3) CA2.v3_2 = true := by
  quickRfl

theorem CA2.c3_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 6, nat_lit 5] CA2.v3_2) (MX (nat_lit 3)) = true := by
  quickRfl

theorem CA2.c3 : chA2 (nat_lit 3) = true :=
  chStep_of (P := J.CA2) (b := nat_lit 0) (k := nat_lit 10) (i := nat_lit 3)
    (w := [nat_lit 7, nat_lit 6, nat_lit 5] ++ ([nat_lit 4, nat_lit 3, nat_lit 1] ++ ([nat_lit 1, nat_lit 2, nat_lit 4] ++ ([nat_lit 3, nat_lit 7, nat_lit 8] ++ ([nat_lit 7, nat_lit 3] ++ [nat_lit 4, nat_lit 2])))))
    (Y := (MX (nat_lit 4))) (Z := (MX (nat_lit 3))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CA2.c3_p6 CA2.c3_p5) CA2.c3_p4) CA2.c3_p3) CA2.c3_p2) CA2.c3_p1)

#kc_natval CA2.v4_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 6, nat_lit 7] (MX (nat_lit 5))

theorem CA2.c4_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 6, nat_lit 7] (MX (nat_lit 5))) CA2.v4_6 = true := by
  quickRfl

#kc_natval CA2.v4_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 4] CA2.v4_6

theorem CA2.c4_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 4] CA2.v4_6) CA2.v4_5 = true := by
  quickRfl

#kc_natval CA2.v4_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 2, nat_lit 3] CA2.v4_5

theorem CA2.c4_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 2, nat_lit 3] CA2.v4_5) CA2.v4_4 = true := by
  quickRfl

#kc_natval CA2.v4_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 4, nat_lit 0] CA2.v4_4

theorem CA2.c4_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 4, nat_lit 0] CA2.v4_4) CA2.v4_3 = true := by
  quickRfl

#kc_natval CA2.v4_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 8, nat_lit 7] CA2.v4_3

theorem CA2.c4_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 8, nat_lit 7] CA2.v4_3) CA2.v4_2 = true := by
  quickRfl

theorem CA2.c4_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 4, nat_lit 3] CA2.v4_2) (MX (nat_lit 4)) = true := by
  quickRfl

theorem CA2.c4 : chA2 (nat_lit 4) = true :=
  chStep_of (P := J.CA2) (b := nat_lit 0) (k := nat_lit 10) (i := nat_lit 4)
    (w := [nat_lit 1, nat_lit 4, nat_lit 3] ++ ([nat_lit 7, nat_lit 8, nat_lit 7] ++ ([nat_lit 3, nat_lit 4, nat_lit 0] ++ ([nat_lit 1, nat_lit 2, nat_lit 3] ++ ([nat_lit 5, nat_lit 4] ++ [nat_lit 6, nat_lit 7])))))
    (Y := (MX (nat_lit 5))) (Z := (MX (nat_lit 4))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CA2.c4_p6 CA2.c4_p5) CA2.c4_p4) CA2.c4_p3) CA2.c4_p2) CA2.c4_p1)

#kc_natval CA2.v5_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7] (MX (nat_lit 6))

theorem CA2.c5_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7] (MX (nat_lit 6))) CA2.v5_6 = true := by
  quickRfl

#kc_natval CA2.v5_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 4] CA2.v5_6

theorem CA2.c5_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 4] CA2.v5_6) CA2.v5_5 = true := by
  quickRfl

#kc_natval CA2.v5_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3, nat_lit 2] CA2.v5_5

theorem CA2.c5_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3, nat_lit 2] CA2.v5_5) CA2.v5_4 = true := by
  quickRfl

#kc_natval CA2.v5_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2, nat_lit 1] CA2.v5_4

theorem CA2.c5_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2, nat_lit 1] CA2.v5_4) CA2.v5_3 = true := by
  quickRfl

#kc_natval CA2.v5_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 0, nat_lit 8, nat_lit 7] CA2.v5_3

theorem CA2.c5_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 0, nat_lit 8, nat_lit 7] CA2.v5_3) CA2.v5_2 = true := by
  quickRfl

theorem CA2.c5_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2, nat_lit 1] CA2.v5_2) (MX (nat_lit 5)) = true := by
  quickRfl

theorem CA2.c5 : chA2 (nat_lit 5) = true :=
  chStep_of (P := J.CA2) (b := nat_lit 0) (k := nat_lit 10) (i := nat_lit 5)
    (w := [nat_lit 3, nat_lit 2, nat_lit 1] ++ ([nat_lit 0, nat_lit 8, nat_lit 7] ++ ([nat_lit 3, nat_lit 2, nat_lit 1] ++ ([nat_lit 4, nat_lit 3, nat_lit 2] ++ ([nat_lit 5, nat_lit 4] ++ [nat_lit 3, nat_lit 7])))))
    (Y := (MX (nat_lit 6))) (Z := (MX (nat_lit 5))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CA2.c5_p6 CA2.c5_p5) CA2.c5_p4) CA2.c5_p3) CA2.c5_p2) CA2.c5_p1)

#kc_natval CA2.v6_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 10, nat_lit 11] (MX (nat_lit 7))

theorem CA2.c6_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 10, nat_lit 11] (MX (nat_lit 7))) CA2.v6_6 = true := by
  quickRfl

#kc_natval CA2.v6_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 0] CA2.v6_6

theorem CA2.c6_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 0] CA2.v6_6) CA2.v6_5 = true := by
  quickRfl

#kc_natval CA2.v6_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3, nat_lit 2] CA2.v6_5

theorem CA2.c6_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3, nat_lit 2] CA2.v6_5) CA2.v6_4 = true := by
  quickRfl

#kc_natval CA2.v6_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 9, nat_lit 6, nat_lit 5] CA2.v6_4

theorem CA2.c6_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 9, nat_lit 6, nat_lit 5] CA2.v6_4) CA2.v6_3 = true := by
  quickRfl

#kc_natval CA2.v6_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 8, nat_lit 7] CA2.v6_3

theorem CA2.c6_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 8, nat_lit 7] CA2.v6_3) CA2.v6_2 = true := by
  quickRfl

theorem CA2.c6_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2, nat_lit 4] CA2.v6_2) (MX (nat_lit 6)) = true := by
  quickRfl

theorem CA2.c6 : chA2 (nat_lit 6) = true :=
  chStep_of (P := J.CA2) (b := nat_lit 0) (k := nat_lit 10) (i := nat_lit 6)
    (w := [nat_lit 3, nat_lit 2, nat_lit 4] ++ ([nat_lit 3, nat_lit 8, nat_lit 7] ++ ([nat_lit 9, nat_lit 6, nat_lit 5] ++ ([nat_lit 4, nat_lit 3, nat_lit 2] ++ ([nat_lit 1, nat_lit 0] ++ [nat_lit 10, nat_lit 11])))))
    (Y := (MX (nat_lit 7))) (Z := (MX (nat_lit 6))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CA2.c6_p6 CA2.c6_p5) CA2.c6_p4) CA2.c6_p3) CA2.c6_p2) CA2.c6_p1)

#kc_natval CA2.v7_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7] (MX (nat_lit 8))

theorem CA2.c7_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7] (MX (nat_lit 8))) CA2.v7_6 = true := by
  quickRfl

#kc_natval CA2.v7_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 2] CA2.v7_6

theorem CA2.c7_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 2] CA2.v7_6) CA2.v7_5 = true := by
  quickRfl

#kc_natval CA2.v7_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 8, nat_lit 3] CA2.v7_5

theorem CA2.c7_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 8, nat_lit 3] CA2.v7_5) CA2.v7_4 = true := by
  quickRfl

#kc_natval CA2.v7_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 6, nat_lit 9] CA2.v7_4

theorem CA2.c7_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 6, nat_lit 9] CA2.v7_4) CA2.v7_3 = true := by
  quickRfl

#kc_natval CA2.v7_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 3, nat_lit 4] CA2.v7_3

theorem CA2.c7_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 3, nat_lit 4] CA2.v7_3) CA2.v7_2 = true := by
  quickRfl

theorem CA2.c7_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 10, nat_lit 0, nat_lit 1] CA2.v7_2) (MX (nat_lit 7)) = true := by
  quickRfl

theorem CA2.c7 : chA2 (nat_lit 7) = true :=
  chStep_of (P := J.CA2) (b := nat_lit 0) (k := nat_lit 10) (i := nat_lit 7)
    (w := [nat_lit 10, nat_lit 0, nat_lit 1] ++ ([nat_lit 2, nat_lit 3, nat_lit 4] ++ ([nat_lit 5, nat_lit 6, nat_lit 9] ++ ([nat_lit 7, nat_lit 8, nat_lit 3] ++ ([nat_lit 4, nat_lit 2] ++ [nat_lit 3, nat_lit 7])))))
    (Y := (MX (nat_lit 8))) (Z := (MX (nat_lit 7))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CA2.c7_p6 CA2.c7_p5) CA2.c7_p4) CA2.c7_p3) CA2.c7_p2) CA2.c7_p1)

#kc_natval CA2.v8_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7] (MX (nat_lit 9))

theorem CA2.c8_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7] (MX (nat_lit 9))) CA2.v8_6 = true := by
  quickRfl

#kc_natval CA2.v8_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 2] CA2.v8_6

theorem CA2.c8_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 2] CA2.v8_6) CA2.v8_5 = true := by
  quickRfl

#kc_natval CA2.v8_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 8, nat_lit 0] CA2.v8_5

theorem CA2.c8_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 8, nat_lit 0] CA2.v8_5) CA2.v8_4 = true := by
  quickRfl

#kc_natval CA2.v8_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 2, nat_lit 3] CA2.v8_4

theorem CA2.c8_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 2, nat_lit 3] CA2.v8_4) CA2.v8_3 = true := by
  quickRfl

#kc_natval CA2.v8_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 3, nat_lit 4] CA2.v8_3

theorem CA2.c8_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 3, nat_lit 4] CA2.v8_3) CA2.v8_2 = true := by
  quickRfl

theorem CA2.c8_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 4, nat_lit 5] CA2.v8_2) (MX (nat_lit 8)) = true := by
  quickRfl

theorem CA2.c8 : chA2 (nat_lit 8) = true :=
  chStep_of (P := J.CA2) (b := nat_lit 0) (k := nat_lit 10) (i := nat_lit 8)
    (w := [nat_lit 3, nat_lit 4, nat_lit 5] ++ ([nat_lit 2, nat_lit 3, nat_lit 4] ++ ([nat_lit 1, nat_lit 2, nat_lit 3] ++ ([nat_lit 7, nat_lit 8, nat_lit 0] ++ ([nat_lit 1, nat_lit 2] ++ [nat_lit 3, nat_lit 7])))))
    (Y := (MX (nat_lit 9))) (Z := (MX (nat_lit 8))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CA2.c8_p6 CA2.c8_p5) CA2.c8_p4) CA2.c8_p3) CA2.c8_p2) CA2.c8_p1)

#kc_natval CA2.v9_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 0, nat_lit 7] CFSG.KD.BrFi24.ONE

theorem CA2.c9_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 0, nat_lit 7] CFSG.KD.BrFi24.ONE) CA2.v9_3 = true := by
  quickRfl

#kc_natval CA2.v9_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2, nat_lit 1] CA2.v9_3

theorem CA2.c9_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2, nat_lit 1] CA2.v9_3) CA2.v9_2 = true := by
  quickRfl

theorem CA2.c9_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 6, nat_lit 4, nat_lit 5] CA2.v9_2) (MX (nat_lit 9)) = true := by
  quickRfl

theorem CA2.c9 : chA2 (nat_lit 9) = true :=
  chStep_of (P := J.CA2) (b := nat_lit 0) (k := nat_lit 10) (i := nat_lit 9)
    (w := [nat_lit 6, nat_lit 4, nat_lit 5] ++ ([nat_lit 3, nat_lit 2, nat_lit 1] ++ [nat_lit 0, nat_lit 7]))
    (Y := CFSG.KD.BrFi24.ONE) (Z := (MX (nat_lit 9))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append CA2.c9_p3 CA2.c9_p2) CA2.c9_p1)

end CFSG.KD.Fi24P7

end
