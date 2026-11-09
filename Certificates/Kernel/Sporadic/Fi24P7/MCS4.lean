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

#kc_natval CS4.v0_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3] (MX (nat_lit 33))

theorem CS4.c0_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3] (MX (nat_lit 33))) CS4.v0_6 = true := by
  quickRfl

#kc_natval CS4.v0_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 1] CS4.v0_6

theorem CS4.c0_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 1] CS4.v0_6) CS4.v0_5 = true := by
  quickRfl

#kc_natval CS4.v0_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 6, nat_lit 7, nat_lit 3] CS4.v0_5

theorem CS4.c0_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 6, nat_lit 7, nat_lit 3] CS4.v0_5) CS4.v0_4 = true := by
  quickRfl

#kc_natval CS4.v0_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 4, nat_lit 5] CS4.v0_4

theorem CS4.c0_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 4, nat_lit 5] CS4.v0_4) CS4.v0_3 = true := by
  quickRfl

#kc_natval CS4.v0_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 0, nat_lit 1, nat_lit 2] CS4.v0_3

theorem CS4.c0_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 0, nat_lit 1, nat_lit 2] CS4.v0_3) CS4.v0_2 = true := by
  quickRfl

theorem CS4.c0_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 11, nat_lit 10, nat_lit 1] CS4.v0_2) (MX (nat_lit 32)) = true := by
  quickRfl

theorem CS4.c0 : chS4 (nat_lit 0) = true :=
  chStep_of (P := J.CS4) (b := nat_lit 32) (k := nat_lit 5) (i := nat_lit 0)
    (w := [nat_lit 11, nat_lit 10, nat_lit 1] ++ ([nat_lit 0, nat_lit 1, nat_lit 2] ++ ([nat_lit 3, nat_lit 4, nat_lit 5] ++ ([nat_lit 6, nat_lit 7, nat_lit 3] ++ ([nat_lit 2, nat_lit 1] ++ [nat_lit 4, nat_lit 3])))))
    (Y := (MX (nat_lit 33))) (Z := (MX (nat_lit 32))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CS4.c0_p6 CS4.c0_p5) CS4.c0_p4) CS4.c0_p3) CS4.c0_p2) CS4.c0_p1)

#kc_natval CS4.v1_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2] (MX (nat_lit 34))

theorem CS4.c1_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2] (MX (nat_lit 34))) CS4.v1_6 = true := by
  quickRfl

#kc_natval CS4.v1_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 7] CS4.v1_6

theorem CS4.c1_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 7] CS4.v1_6) CS4.v1_5 = true := by
  quickRfl

#kc_natval CS4.v1_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 1, nat_lit 5] CS4.v1_5

theorem CS4.c1_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 1, nat_lit 5] CS4.v1_5) CS4.v1_4 = true := by
  quickRfl

#kc_natval CS4.v1_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 0, nat_lit 4, nat_lit 3] CS4.v1_4

theorem CS4.c1_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 0, nat_lit 4, nat_lit 3] CS4.v1_4) CS4.v1_3 = true := by
  quickRfl

#kc_natval CS4.v1_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2, nat_lit 1] CS4.v1_3

theorem CS4.c1_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2, nat_lit 1] CS4.v1_3) CS4.v1_2 = true := by
  quickRfl

theorem CS4.c1_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 8, nat_lit 7] CS4.v1_2) (MX (nat_lit 33)) = true := by
  quickRfl

theorem CS4.c1 : chS4 (nat_lit 1) = true :=
  chStep_of (P := J.CS4) (b := nat_lit 32) (k := nat_lit 5) (i := nat_lit 1)
    (w := [nat_lit 5, nat_lit 8, nat_lit 7] ++ ([nat_lit 3, nat_lit 2, nat_lit 1] ++ ([nat_lit 0, nat_lit 4, nat_lit 3] ++ ([nat_lit 2, nat_lit 1, nat_lit 5] ++ ([nat_lit 4, nat_lit 7] ++ [nat_lit 3, nat_lit 2])))))
    (Y := (MX (nat_lit 34))) (Z := (MX (nat_lit 33))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CS4.c1_p6 CS4.c1_p5) CS4.c1_p4) CS4.c1_p3) CS4.c1_p2) CS4.c1_p1)

#kc_natval CS4.v2_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7] (MX (nat_lit 35))

theorem CS4.c2_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7] (MX (nat_lit 35))) CS4.v2_6 = true := by
  quickRfl

#kc_natval CS4.v2_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 8, nat_lit 2] CS4.v2_6

theorem CS4.c2_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 8, nat_lit 2] CS4.v2_6) CS4.v2_5 = true := by
  quickRfl

#kc_natval CS4.v2_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3, nat_lit 7] CS4.v2_5

theorem CS4.c2_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 3, nat_lit 7] CS4.v2_5) CS4.v2_4 = true := by
  quickRfl

#kc_natval CS4.v2_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 9, nat_lit 6, nat_lit 5] CS4.v2_4

theorem CS4.c2_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 9, nat_lit 6, nat_lit 5] CS4.v2_4) CS4.v2_3 = true := by
  quickRfl

#kc_natval CS4.v2_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 5, nat_lit 6] CS4.v2_3

theorem CS4.c2_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 5, nat_lit 6] CS4.v2_3) CS4.v2_2 = true := by
  quickRfl

theorem CS4.c2_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 8, nat_lit 7, nat_lit 3] CS4.v2_2) (MX (nat_lit 34)) = true := by
  quickRfl

theorem CS4.c2 : chS4 (nat_lit 2) = true :=
  chStep_of (P := J.CS4) (b := nat_lit 32) (k := nat_lit 5) (i := nat_lit 2)
    (w := [nat_lit 8, nat_lit 7, nat_lit 3] ++ ([nat_lit 4, nat_lit 5, nat_lit 6] ++ ([nat_lit 9, nat_lit 6, nat_lit 5] ++ ([nat_lit 4, nat_lit 3, nat_lit 7] ++ ([nat_lit 8, nat_lit 2] ++ [nat_lit 3, nat_lit 7])))))
    (Y := (MX (nat_lit 35))) (Z := (MX (nat_lit 34))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CS4.c2_p6 CS4.c2_p5) CS4.c2_p4) CS4.c2_p3) CS4.c2_p2) CS4.c2_p1)

#kc_natval CS4.v3_6 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 1] (MX (nat_lit 36))

theorem CS4.c3_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 1] (MX (nat_lit 36))) CS4.v3_6 = true := by
  quickRfl

#kc_natval CS4.v3_5 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 3] CS4.v3_6

theorem CS4.c3_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 5, nat_lit 3] CS4.v3_6) CS4.v3_5 = true := by
  quickRfl

#kc_natval CS4.v3_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7, nat_lit 8] CS4.v3_5

theorem CS4.c3_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 7, nat_lit 8] CS4.v3_5) CS4.v3_4 = true := by
  quickRfl

#kc_natval CS4.v3_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 0, nat_lit 1, nat_lit 2] CS4.v3_4

theorem CS4.c3_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 0, nat_lit 1, nat_lit 2] CS4.v3_4) CS4.v3_3 = true := by
  quickRfl

#kc_natval CS4.v3_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 3, nat_lit 4] CS4.v3_3

theorem CS4.c3_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 3, nat_lit 4] CS4.v3_3) CS4.v3_2 = true := by
  quickRfl

theorem CS4.c3_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 4, nat_lit 5, nat_lit 1] CS4.v3_2) (MX (nat_lit 35)) = true := by
  quickRfl

theorem CS4.c3 : chS4 (nat_lit 3) = true :=
  chStep_of (P := J.CS4) (b := nat_lit 32) (k := nat_lit 5) (i := nat_lit 3)
    (w := [nat_lit 4, nat_lit 5, nat_lit 1] ++ ([nat_lit 2, nat_lit 3, nat_lit 4] ++ ([nat_lit 0, nat_lit 1, nat_lit 2] ++ ([nat_lit 3, nat_lit 7, nat_lit 8] ++ ([nat_lit 5, nat_lit 3] ++ [nat_lit 4, nat_lit 1])))))
    (Y := (MX (nat_lit 36))) (Z := (MX (nat_lit 35))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CS4.c3_p6 CS4.c3_p5) CS4.c3_p4) CS4.c3_p3) CS4.c3_p2) CS4.c3_p1)

#kc_natval CS4.v4_4 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 0] CFSG.KD.BrFi24.ONE

theorem CS4.c4_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 1, nat_lit 0] CFSG.KD.BrFi24.ONE) CS4.v4_4 = true := by
  quickRfl

#kc_natval CS4.v4_3 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2] CS4.v4_4

theorem CS4.c4_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 3, nat_lit 2] CS4.v4_4) CS4.v4_3 = true := by
  quickRfl

#kc_natval CS4.v4_2 := CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 6, nat_lit 5, nat_lit 4] CS4.v4_3

theorem CS4.c4_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 6, nat_lit 5, nat_lit 4] CS4.v4_3) CS4.v4_2 = true := by
  quickRfl

theorem CS4.c4_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG [nat_lit 2, nat_lit 3, nat_lit 7] CS4.v4_2) (MX (nat_lit 36)) = true := by
  quickRfl

theorem CS4.c4 : chS4 (nat_lit 4) = true :=
  chStep_of (P := J.CS4) (b := nat_lit 32) (k := nat_lit 5) (i := nat_lit 4)
    (w := [nat_lit 2, nat_lit 3, nat_lit 7] ++ ([nat_lit 6, nat_lit 5, nat_lit 4] ++ ([nat_lit 3, nat_lit 2] ++ [nat_lit 1, nat_lit 0])))
    (Y := CFSG.KD.BrFi24.ONE) (Z := (MX (nat_lit 36))) rfl rfl rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append CS4.c4_p4 CS4.c4_p3) CS4.c4_p2) CS4.c4_p1)

end CFSG.KD.Fi24P7

end
