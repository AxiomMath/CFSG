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

#kc_natval CA4.v0_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3] (MX (nat_lit 11))

theorem CA4.c0_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3] (MX (nat_lit 11))) CA4.v0_6 = true := by
  quickRfl

#kc_natval CA4.v0_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 5] CA4.v0_6

theorem CA4.c0_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 5] CA4.v0_6) CA4.v0_5 = true := by
  quickRfl

#kc_natval CA4.v0_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7, nat_lit 8] CA4.v0_5

theorem CA4.c0_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7, nat_lit 8] CA4.v0_5) CA4.v0_4 = true := by
  quickRfl

#kc_natval CA4.v0_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2, nat_lit 4] CA4.v0_4

theorem CA4.c0_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2, nat_lit 4] CA4.v0_4) CA4.v0_3 = true := by
  quickRfl

#kc_natval CA4.v0_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 1, nat_lit 7] CA4.v0_3

theorem CA4.c0_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 1, nat_lit 7] CA4.v0_3) CA4.v0_2 = true := by
  quickRfl

theorem CA4.c0_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 8, nat_lit 1, nat_lit 3] CA4.v0_2) (MX (nat_lit 10)) = true := by
  quickRfl

theorem CA4.c0 : chA4 (nat_lit 0) = true :=
  chStep_of (P := J.CA4) (b := nat_lit 10) (k := nat_lit 11) (i := nat_lit 0)
    (w := [nat_lit 8, nat_lit 1, nat_lit 3] ++ ([nat_lit 2, nat_lit 1, nat_lit 7] ++ ([nat_lit 3, nat_lit 2, nat_lit 4] ++ ([nat_lit 3, nat_lit 7, nat_lit 8] ++ ([nat_lit 2, nat_lit 5] ++ [nat_lit 4, nat_lit 3])))))
    (Y := (MX (nat_lit 11))) (Z := (MX (nat_lit 10))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CA4.c0_p6 CA4.c0_p5) CA4.c0_p4) CA4.c0_p3) CA4.c0_p2) CA4.c0_p1)

#kc_natval CA4.v1_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 5] (MX (nat_lit 12))

theorem CA4.c1_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 5] (MX (nat_lit 12))) CA4.v1_6 = true := by
  quickRfl

#kc_natval CA4.v1_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 3] CA4.v1_6

theorem CA4.c1_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 3] CA4.v1_6) CA4.v1_5 = true := by
  quickRfl

#kc_natval CA4.v1_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 9, nat_lit 0, nat_lit 1] CA4.v1_5

theorem CA4.c1_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 9, nat_lit 0, nat_lit 1] CA4.v1_5) CA4.v1_4 = true := by
  quickRfl

#kc_natval CA4.v1_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7, nat_lit 8] CA4.v1_4

theorem CA4.c1_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7, nat_lit 8] CA4.v1_4) CA4.v1_3 = true := by
  quickRfl

#kc_natval CA4.v1_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 6, nat_lit 5, nat_lit 4] CA4.v1_3

theorem CA4.c1_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 6, nat_lit 5, nat_lit 4] CA4.v1_3) CA4.v1_2 = true := by
  quickRfl

theorem CA4.c1_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 2, nat_lit 1] CA4.v1_2) (MX (nat_lit 11)) = true := by
  quickRfl

theorem CA4.c1 : chA4 (nat_lit 1) = true :=
  chStep_of (P := J.CA4) (b := nat_lit 10) (k := nat_lit 11) (i := nat_lit 1)
    (w := [nat_lit 7, nat_lit 2, nat_lit 1] ++ ([nat_lit 6, nat_lit 5, nat_lit 4] ++ ([nat_lit 3, nat_lit 7, nat_lit 8] ++ ([nat_lit 9, nat_lit 0, nat_lit 1] ++ ([nat_lit 2, nat_lit 3] ++ [nat_lit 4, nat_lit 5])))))
    (Y := (MX (nat_lit 12))) (Z := (MX (nat_lit 11))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CA4.c1_p6 CA4.c1_p5) CA4.c1_p4) CA4.c1_p3) CA4.c1_p2) CA4.c1_p1)

#kc_natval CA4.v2_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3] (MX (nat_lit 13))

theorem CA4.c2_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3] (MX (nat_lit 13))) CA4.v2_6 = true := by
  quickRfl

#kc_natval CA4.v2_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 0] CA4.v2_6

theorem CA4.c2_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 0] CA4.v2_6) CA4.v2_5 = true := by
  quickRfl

#kc_natval CA4.v2_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 3, nat_lit 2] CA4.v2_5

theorem CA4.c2_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 3, nat_lit 2] CA4.v2_5) CA4.v2_4 = true := by
  quickRfl

#kc_natval CA4.v2_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 5, nat_lit 8] CA4.v2_4

theorem CA4.c2_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 5, nat_lit 8] CA4.v2_4) CA4.v2_3 = true := by
  quickRfl

#kc_natval CA4.v2_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 1, nat_lit 4] CA4.v2_3

theorem CA4.c2_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 1, nat_lit 4] CA4.v2_3) CA4.v2_2 = true := by
  quickRfl

theorem CA4.c2_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 6, nat_lit 7, nat_lit 3] CA4.v2_2) (MX (nat_lit 12)) = true := by
  quickRfl

theorem CA4.c2 : chA4 (nat_lit 2) = true :=
  chStep_of (P := J.CA4) (b := nat_lit 10) (k := nat_lit 11) (i := nat_lit 2)
    (w := [nat_lit 6, nat_lit 7, nat_lit 3] ++ ([nat_lit 2, nat_lit 1, nat_lit 4] ++ ([nat_lit 3, nat_lit 5, nat_lit 8] ++ ([nat_lit 7, nat_lit 3, nat_lit 2] ++ ([nat_lit 1, nat_lit 0] ++ [nat_lit 4, nat_lit 3])))))
    (Y := (MX (nat_lit 13))) (Z := (MX (nat_lit 12))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CA4.c2_p6 CA4.c2_p5) CA4.c2_p4) CA4.c2_p3) CA4.c2_p2) CA4.c2_p1)

#kc_natval CA4.v3_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 6, nat_lit 5] (MX (nat_lit 14))

theorem CA4.c3_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 6, nat_lit 5] (MX (nat_lit 14))) CA4.v3_6 = true := by
  quickRfl

#kc_natval CA4.v3_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 6, nat_lit 9] CA4.v3_6

theorem CA4.c3_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 6, nat_lit 9] CA4.v3_6) CA4.v3_5 = true := by
  quickRfl

#kc_natval CA4.v3_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 4, nat_lit 5] CA4.v3_5

theorem CA4.c3_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 4, nat_lit 5] CA4.v3_5) CA4.v3_4 = true := by
  quickRfl

#kc_natval CA4.v3_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 8, nat_lit 7] CA4.v3_4

theorem CA4.c3_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 8, nat_lit 7] CA4.v3_4) CA4.v3_3 = true := by
  quickRfl

#kc_natval CA4.v3_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 7, nat_lit 3] CA4.v3_3

theorem CA4.c3_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 7, nat_lit 3] CA4.v3_3) CA4.v3_2 = true := by
  quickRfl

theorem CA4.c3_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 1, nat_lit 5] CA4.v3_2) (MX (nat_lit 13)) = true := by
  quickRfl

theorem CA4.c3 : chA4 (nat_lit 3) = true :=
  chStep_of (P := J.CA4) (b := nat_lit 10) (k := nat_lit 11) (i := nat_lit 3)
    (w := [nat_lit 2, nat_lit 1, nat_lit 5] ++ ([nat_lit 4, nat_lit 7, nat_lit 3] ++ ([nat_lit 2, nat_lit 8, nat_lit 7] ++ ([nat_lit 3, nat_lit 4, nat_lit 5] ++ ([nat_lit 6, nat_lit 9] ++ [nat_lit 6, nat_lit 5])))))
    (Y := (MX (nat_lit 14))) (Z := (MX (nat_lit 13))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CA4.c3_p6 CA4.c3_p5) CA4.c3_p4) CA4.c3_p3) CA4.c3_p2) CA4.c3_p1)

#kc_natval CA4.v4_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 2] (MX (nat_lit 15))

theorem CA4.c4_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 2] (MX (nat_lit 15))) CA4.v4_6 = true := by
  quickRfl

#kc_natval CA4.v4_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 0] CA4.v4_6

theorem CA4.c4_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 0] CA4.v4_6) CA4.v4_5 = true := by
  quickRfl

#kc_natval CA4.v4_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 2, nat_lit 3] CA4.v4_5

theorem CA4.c4_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 2, nat_lit 3] CA4.v4_5) CA4.v4_4 = true := by
  quickRfl

#kc_natval CA4.v4_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 4, nat_lit 5] CA4.v4_4

theorem CA4.c4_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 4, nat_lit 5] CA4.v4_4) CA4.v4_3 = true := by
  quickRfl

#kc_natval CA4.v4_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 8, nat_lit 2, nat_lit 3] CA4.v4_3

theorem CA4.c4_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 8, nat_lit 2, nat_lit 3] CA4.v4_3) CA4.v4_2 = true := by
  quickRfl

theorem CA4.c4_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3, nat_lit 7] CA4.v4_2) (MX (nat_lit 14)) = true := by
  quickRfl

theorem CA4.c4 : chA4 (nat_lit 4) = true :=
  chStep_of (P := J.CA4) (b := nat_lit 10) (k := nat_lit 11) (i := nat_lit 4)
    (w := [nat_lit 4, nat_lit 3, nat_lit 7] ++ ([nat_lit 8, nat_lit 2, nat_lit 3] ++ ([nat_lit 7, nat_lit 4, nat_lit 5] ++ ([nat_lit 1, nat_lit 2, nat_lit 3] ++ ([nat_lit 4, nat_lit 0] ++ [nat_lit 1, nat_lit 2])))))
    (Y := (MX (nat_lit 15))) (Z := (MX (nat_lit 14))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CA4.c4_p6 CA4.c4_p5) CA4.c4_p4) CA4.c4_p3) CA4.c4_p2) CA4.c4_p1)

#kc_natval CA4.v5_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 1] (MX (nat_lit 16))

theorem CA4.c5_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 1] (MX (nat_lit 16))) CA4.v5_6 = true := by
  quickRfl

#kc_natval CA4.v5_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3] CA4.v5_6

theorem CA4.c5_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3] CA4.v5_6) CA4.v5_5 = true := by
  quickRfl

#kc_natval CA4.v5_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 6, nat_lit 5] CA4.v5_5

theorem CA4.c5_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 7, nat_lit 6, nat_lit 5] CA4.v5_5) CA4.v5_4 = true := by
  quickRfl

#kc_natval CA4.v5_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 2, nat_lit 3] CA4.v5_4

theorem CA4.c5_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 2, nat_lit 3] CA4.v5_4) CA4.v5_3 = true := by
  quickRfl

#kc_natval CA4.v5_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 3, nat_lit 4] CA4.v5_3

theorem CA4.c5_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 3, nat_lit 4] CA4.v5_3) CA4.v5_2 = true := by
  quickRfl

theorem CA4.c5_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7, nat_lit 8] CA4.v5_2) (MX (nat_lit 15)) = true := by
  quickRfl

theorem CA4.c5 : chA4 (nat_lit 5) = true :=
  chStep_of (P := J.CA4) (b := nat_lit 10) (k := nat_lit 11) (i := nat_lit 5)
    (w := [nat_lit 3, nat_lit 7, nat_lit 8] ++ ([nat_lit 5, nat_lit 3, nat_lit 4] ++ ([nat_lit 1, nat_lit 2, nat_lit 3] ++ ([nat_lit 7, nat_lit 6, nat_lit 5] ++ ([nat_lit 4, nat_lit 3] ++ [nat_lit 2, nat_lit 1])))))
    (Y := (MX (nat_lit 16))) (Z := (MX (nat_lit 15))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CA4.c5_p6 CA4.c5_p5) CA4.c5_p4) CA4.c5_p3) CA4.c5_p2) CA4.c5_p1)

#kc_natval CA4.v6_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3] (MX (nat_lit 17))

theorem CA4.c6_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3] (MX (nat_lit 17))) CA4.v6_6 = true := by
  quickRfl

#kc_natval CA4.v6_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 1] CA4.v6_6

theorem CA4.c6_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 1] CA4.v6_6) CA4.v6_5 = true := by
  quickRfl

#kc_natval CA4.v6_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 6, nat_lit 7, nat_lit 3] CA4.v6_5

theorem CA4.c6_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 6, nat_lit 7, nat_lit 3] CA4.v6_5) CA4.v6_4 = true := by
  quickRfl

#kc_natval CA4.v6_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 4, nat_lit 5] CA4.v6_4

theorem CA4.c6_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 4, nat_lit 5] CA4.v6_4) CA4.v6_3 = true := by
  quickRfl

#kc_natval CA4.v6_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 0, nat_lit 1, nat_lit 2] CA4.v6_3

theorem CA4.c6_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 0, nat_lit 1, nat_lit 2] CA4.v6_3) CA4.v6_2 = true := by
  quickRfl

theorem CA4.c6_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 0, nat_lit 3, nat_lit 8] CA4.v6_2) (MX (nat_lit 16)) = true := by
  quickRfl

theorem CA4.c6 : chA4 (nat_lit 6) = true :=
  chStep_of (P := J.CA4) (b := nat_lit 10) (k := nat_lit 11) (i := nat_lit 6)
    (w := [nat_lit 0, nat_lit 3, nat_lit 8] ++ ([nat_lit 0, nat_lit 1, nat_lit 2] ++ ([nat_lit 3, nat_lit 4, nat_lit 5] ++ ([nat_lit 6, nat_lit 7, nat_lit 3] ++ ([nat_lit 2, nat_lit 1] ++ [nat_lit 4, nat_lit 3])))))
    (Y := (MX (nat_lit 17))) (Z := (MX (nat_lit 16))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CA4.c6_p6 CA4.c6_p5) CA4.c6_p4) CA4.c6_p3) CA4.c6_p2) CA4.c6_p1)

#kc_natval CA4.v7_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2] (MX (nat_lit 18))

theorem CA4.c7_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2] (MX (nat_lit 18))) CA4.v7_6 = true := by
  quickRfl

#kc_natval CA4.v7_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 7] CA4.v7_6

theorem CA4.c7_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 7] CA4.v7_6) CA4.v7_5 = true := by
  quickRfl

#kc_natval CA4.v7_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 1, nat_lit 5] CA4.v7_5

theorem CA4.c7_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 1, nat_lit 5] CA4.v7_5) CA4.v7_4 = true := by
  quickRfl

#kc_natval CA4.v7_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 0, nat_lit 4, nat_lit 3] CA4.v7_4

theorem CA4.c7_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 0, nat_lit 4, nat_lit 3] CA4.v7_4) CA4.v7_3 = true := by
  quickRfl

#kc_natval CA4.v7_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2, nat_lit 1] CA4.v7_3

theorem CA4.c7_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2, nat_lit 1] CA4.v7_3) CA4.v7_2 = true := by
  quickRfl

theorem CA4.c7_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 8, nat_lit 7] CA4.v7_2) (MX (nat_lit 17)) = true := by
  quickRfl

theorem CA4.c7 : chA4 (nat_lit 7) = true :=
  chStep_of (P := J.CA4) (b := nat_lit 10) (k := nat_lit 11) (i := nat_lit 7)
    (w := [nat_lit 5, nat_lit 8, nat_lit 7] ++ ([nat_lit 3, nat_lit 2, nat_lit 1] ++ ([nat_lit 0, nat_lit 4, nat_lit 3] ++ ([nat_lit 2, nat_lit 1, nat_lit 5] ++ ([nat_lit 4, nat_lit 7] ++ [nat_lit 3, nat_lit 2])))))
    (Y := (MX (nat_lit 18))) (Z := (MX (nat_lit 17))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CA4.c7_p6 CA4.c7_p5) CA4.c7_p4) CA4.c7_p3) CA4.c7_p2) CA4.c7_p1)

#kc_natval CA4.v8_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7] (MX (nat_lit 19))

theorem CA4.c8_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7] (MX (nat_lit 19))) CA4.v8_6 = true := by
  quickRfl

#kc_natval CA4.v8_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 8, nat_lit 2] CA4.v8_6

theorem CA4.c8_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 8, nat_lit 2] CA4.v8_6) CA4.v8_5 = true := by
  quickRfl

#kc_natval CA4.v8_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3, nat_lit 7] CA4.v8_5

theorem CA4.c8_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3, nat_lit 7] CA4.v8_5) CA4.v8_4 = true := by
  quickRfl

#kc_natval CA4.v8_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 9, nat_lit 6, nat_lit 5] CA4.v8_4

theorem CA4.c8_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 9, nat_lit 6, nat_lit 5] CA4.v8_4) CA4.v8_3 = true := by
  quickRfl

#kc_natval CA4.v8_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 5, nat_lit 6] CA4.v8_3

theorem CA4.c8_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 5, nat_lit 6] CA4.v8_3) CA4.v8_2 = true := by
  quickRfl

theorem CA4.c8_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 8, nat_lit 7, nat_lit 3] CA4.v8_2) (MX (nat_lit 18)) = true := by
  quickRfl

theorem CA4.c8 : chA4 (nat_lit 8) = true :=
  chStep_of (P := J.CA4) (b := nat_lit 10) (k := nat_lit 11) (i := nat_lit 8)
    (w := [nat_lit 8, nat_lit 7, nat_lit 3] ++ ([nat_lit 4, nat_lit 5, nat_lit 6] ++ ([nat_lit 9, nat_lit 6, nat_lit 5] ++ ([nat_lit 4, nat_lit 3, nat_lit 7] ++ ([nat_lit 8, nat_lit 2] ++ [nat_lit 3, nat_lit 7])))))
    (Y := (MX (nat_lit 19))) (Z := (MX (nat_lit 18))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CA4.c8_p6 CA4.c8_p5) CA4.c8_p4) CA4.c8_p3) CA4.c8_p2) CA4.c8_p1)

#kc_natval CA4.v9_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 1] (MX (nat_lit 20))

theorem CA4.c9_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 1] (MX (nat_lit 20))) CA4.v9_6 = true := by
  quickRfl

#kc_natval CA4.v9_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 3] CA4.v9_6

theorem CA4.c9_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 3] CA4.v9_6) CA4.v9_5 = true := by
  quickRfl

#kc_natval CA4.v9_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7, nat_lit 8] CA4.v9_5

theorem CA4.c9_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7, nat_lit 8] CA4.v9_5) CA4.v9_4 = true := by
  quickRfl

#kc_natval CA4.v9_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 0, nat_lit 1, nat_lit 2] CA4.v9_4

theorem CA4.c9_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 0, nat_lit 1, nat_lit 2] CA4.v9_4) CA4.v9_3 = true := by
  quickRfl

#kc_natval CA4.v9_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 3, nat_lit 4] CA4.v9_3

theorem CA4.c9_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 3, nat_lit 4] CA4.v9_3) CA4.v9_2 = true := by
  quickRfl

theorem CA4.c9_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 5, nat_lit 1] CA4.v9_2) (MX (nat_lit 19)) = true := by
  quickRfl

theorem CA4.c9 : chA4 (nat_lit 9) = true :=
  chStep_of (P := J.CA4) (b := nat_lit 10) (k := nat_lit 11) (i := nat_lit 9)
    (w := [nat_lit 4, nat_lit 5, nat_lit 1] ++ ([nat_lit 2, nat_lit 3, nat_lit 4] ++ ([nat_lit 0, nat_lit 1, nat_lit 2] ++ ([nat_lit 3, nat_lit 7, nat_lit 8] ++ ([nat_lit 5, nat_lit 3] ++ [nat_lit 4, nat_lit 1])))))
    (Y := (MX (nat_lit 20))) (Z := (MX (nat_lit 19))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CA4.c9_p6 CA4.c9_p5) CA4.c9_p4) CA4.c9_p3) CA4.c9_p2) CA4.c9_p1)

#kc_natval CA4.v10_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 0] CFSG.KD.BrFi24.ONE

theorem CA4.c10_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 0] CFSG.KD.BrFi24.ONE) CA4.v10_4 = true := by
  quickRfl

#kc_natval CA4.v10_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2] CA4.v10_4

theorem CA4.c10_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2] CA4.v10_4) CA4.v10_3 = true := by
  quickRfl

#kc_natval CA4.v10_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 6, nat_lit 5, nat_lit 4] CA4.v10_3

theorem CA4.c10_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 6, nat_lit 5, nat_lit 4] CA4.v10_3) CA4.v10_2 = true := by
  quickRfl

theorem CA4.c10_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 3, nat_lit 7] CA4.v10_2) (MX (nat_lit 20)) = true := by
  quickRfl

theorem CA4.c10 : chA4 (nat_lit 10) = true :=
  chStep_of (P := J.CA4) (b := nat_lit 10) (k := nat_lit 11) (i := nat_lit 10)
    (w := [nat_lit 2, nat_lit 3, nat_lit 7] ++ ([nat_lit 6, nat_lit 5, nat_lit 4] ++ ([nat_lit 3, nat_lit 2] ++ [nat_lit 1, nat_lit 0])))
    (Y := CFSG.KD.BrFi24.ONE) (Z := (MX (nat_lit 20))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CA4.c10_p4 CA4.c10_p3) CA4.c10_p2) CA4.c10_p1)

end CFSG.KD.Fi24P7

end
