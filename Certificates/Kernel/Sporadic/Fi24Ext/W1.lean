module

public import Certificates.Kernel.Sporadic.Fi24Ext.Chunks
public import Certificates.Kernel.Sporadic.Fi24Fix.Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree CFSG.KD.Fi24Ext SW1 "Certificates/Kernel/Sporadic/Fi24Ext/data/w1.bin" 152491 4 10826861 14751608447140618479

public section

set_option Elab.async false

open CFSG.KC.Fi24Fix (beq_wordMul_append beq_wordMul_of_eq)

namespace CFSG.KD.Fi24Ext

theorem c6_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 5]
    (SW1 (nat_lit 18))) (ST (nat_lit 6)) = true := by
  quickRfl

theorem c6_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 5]
    (SW1 (nat_lit 17))) (SW1 (nat_lit 18)) = true := by
  quickRfl

theorem c6_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 3]
    (SW1 (nat_lit 16))) (SW1 (nat_lit 17)) = true := by
  quickRfl

theorem c6_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 18]
    (SW1 (nat_lit 15))) (SW1 (nat_lit 16)) = true := by
  quickRfl

theorem c6_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 5]
    (SW1 (nat_lit 14))) (SW1 (nat_lit 15)) = true := by
  quickRfl

theorem c6_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 3]
    (SW1 (nat_lit 13))) (SW1 (nat_lit 14)) = true := by
  quickRfl

theorem c6_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 3]
    (SW1 (nat_lit 12))) (SW1 (nat_lit 13)) = true := by
  quickRfl

theorem c6_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 18]
    (SW1 (nat_lit 11))) (SW1 (nat_lit 12)) = true := by
  quickRfl

theorem c6_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 3]
    (SW1 (nat_lit 10))) (SW1 (nat_lit 11)) = true := by
  quickRfl

theorem c6_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 3]
    (SW1 (nat_lit 9))) (SW1 (nat_lit 10)) = true := by
  quickRfl

theorem c6_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 5]
    (SW1 (nat_lit 8))) (SW1 (nat_lit 9)) = true := by
  quickRfl

theorem c6_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 4]
    (SW1 (nat_lit 7))) (SW1 (nat_lit 8)) = true := by
  quickRfl

theorem c6_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 3]
    (SW1 (nat_lit 6))) (SW1 (nat_lit 7)) = true := by
  quickRfl

theorem c6_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 17]
    (SW1 (nat_lit 5))) (SW1 (nat_lit 6)) = true := by
  quickRfl

theorem c6_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 17]
    (SW1 (nat_lit 4))) (SW1 (nat_lit 5)) = true := by
  quickRfl

theorem c6_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 4]
    (SW1 (nat_lit 3))) (SW1 (nat_lit 4)) = true := by
  quickRfl

theorem c6_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 3]
    (SW1 (nat_lit 2))) (SW1 (nat_lit 3)) = true := by
  quickRfl

theorem c6_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 4]
    (SW1 (nat_lit 1))) (SW1 (nat_lit 2)) = true := by
  quickRfl

theorem c6_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 17]
    (SW1 (nat_lit 0))) (SW1 (nat_lit 1)) = true := by
  quickRfl

theorem c6_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 18]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 6))) (SW1 (nat_lit 0)) = true := by
  quickRfl

theorem c6_w : WC (nat_lit 6) = [3, 5] ++ ([4, 5] ++ ([4, 3] ++ ([17, 18] ++ ([3, 5] ++ ([17, 3] ++ ([5, 3] ++ ([18, 18] ++ ([4, 3] ++ ([17, 3] ++ ([17, 5] ++ ([5, 4] ++ ([4, 3] ++ ([18, 17] ++ ([3, 17] ++ ([5, 4] ++ ([18, 3] ++ ([4, 4] ++ ([3, 17] ++ ([17, 18]))))))))))))))))))) := rfl

theorem c6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 6))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 6))) (ST (nat_lit 6)) = true :=
  beq_wordMul_of_eq c6_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c6_p19 c6_p18) c6_p17) c6_p16) c6_p15) c6_p14) c6_p13) c6_p12) c6_p11) c6_p10) c6_p9) c6_p8) c6_p7) c6_p6) c6_p5) c6_p4) c6_p3) c6_p2) c6_p1) c6_p0)

theorem c7_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3]
    (SW1 (nat_lit 32))) (ST (nat_lit 7)) = true := by
  quickRfl

theorem c7_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 3]
    (SW1 (nat_lit 31))) (SW1 (nat_lit 32)) = true := by
  quickRfl

theorem c7_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 18]
    (SW1 (nat_lit 30))) (SW1 (nat_lit 31)) = true := by
  quickRfl

theorem c7_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 4]
    (SW1 (nat_lit 29))) (SW1 (nat_lit 30)) = true := by
  quickRfl

theorem c7_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 4]
    (SW1 (nat_lit 28))) (SW1 (nat_lit 29)) = true := by
  quickRfl

theorem c7_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 4]
    (SW1 (nat_lit 27))) (SW1 (nat_lit 28)) = true := by
  quickRfl

theorem c7_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 18]
    (SW1 (nat_lit 26))) (SW1 (nat_lit 27)) = true := by
  quickRfl

theorem c7_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 4]
    (SW1 (nat_lit 25))) (SW1 (nat_lit 26)) = true := by
  quickRfl

theorem c7_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 5]
    (SW1 (nat_lit 24))) (SW1 (nat_lit 25)) = true := by
  quickRfl

theorem c7_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 4]
    (SW1 (nat_lit 23))) (SW1 (nat_lit 24)) = true := by
  quickRfl

theorem c7_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 17]
    (SW1 (nat_lit 22))) (SW1 (nat_lit 23)) = true := by
  quickRfl

theorem c7_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 17]
    (SW1 (nat_lit 21))) (SW1 (nat_lit 22)) = true := by
  quickRfl

theorem c7_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 5]
    (SW1 (nat_lit 20))) (SW1 (nat_lit 21)) = true := by
  quickRfl

theorem c7_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 4]
    (SW1 (nat_lit 19))) (SW1 (nat_lit 20)) = true := by
  quickRfl

theorem c7_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 17]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 7))) (SW1 (nat_lit 19)) = true := by
  quickRfl

theorem c7_w : WC (nat_lit 7) = [3] ++ ([18, 3] ++ ([17, 18] ++ ([3, 4] ++ ([3, 4] ++ ([18, 4] ++ ([3, 18] ++ ([3, 4] ++ ([3, 5] ++ ([3, 4] ++ ([3, 17] ++ ([17, 17] ++ ([17, 5] ++ ([3, 4] ++ ([3, 17])))))))))))))) := rfl

theorem c7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 7))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 7))) (ST (nat_lit 7)) = true :=
  beq_wordMul_of_eq c7_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c7_p14 c7_p13) c7_p12) c7_p11) c7_p10) c7_p9) c7_p8) c7_p7) c7_p6) c7_p5) c7_p4) c7_p3) c7_p2) c7_p1) c7_p0)

theorem c8_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 18]
    (SW1 (nat_lit 51))) (ST (nat_lit 8)) = true := by
  quickRfl

theorem c8_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 17]
    (SW1 (nat_lit 50))) (SW1 (nat_lit 51)) = true := by
  quickRfl

theorem c8_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 4]
    (SW1 (nat_lit 49))) (SW1 (nat_lit 50)) = true := by
  quickRfl

theorem c8_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 6]
    (SW1 (nat_lit 48))) (SW1 (nat_lit 49)) = true := by
  quickRfl

theorem c8_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 6]
    (SW1 (nat_lit 47))) (SW1 (nat_lit 48)) = true := by
  quickRfl

theorem c8_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 3]
    (SW1 (nat_lit 46))) (SW1 (nat_lit 47)) = true := by
  quickRfl

theorem c8_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 5]
    (SW1 (nat_lit 45))) (SW1 (nat_lit 46)) = true := by
  quickRfl

theorem c8_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 3]
    (SW1 (nat_lit 44))) (SW1 (nat_lit 45)) = true := by
  quickRfl

theorem c8_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 18]
    (SW1 (nat_lit 43))) (SW1 (nat_lit 44)) = true := by
  quickRfl

theorem c8_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 3]
    (SW1 (nat_lit 42))) (SW1 (nat_lit 43)) = true := by
  quickRfl

theorem c8_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 18]
    (SW1 (nat_lit 41))) (SW1 (nat_lit 42)) = true := by
  quickRfl

theorem c8_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 6]
    (SW1 (nat_lit 40))) (SW1 (nat_lit 41)) = true := by
  quickRfl

theorem c8_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 6]
    (SW1 (nat_lit 39))) (SW1 (nat_lit 40)) = true := by
  quickRfl

theorem c8_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 5]
    (SW1 (nat_lit 38))) (SW1 (nat_lit 39)) = true := by
  quickRfl

theorem c8_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 18]
    (SW1 (nat_lit 37))) (SW1 (nat_lit 38)) = true := by
  quickRfl

theorem c8_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 3]
    (SW1 (nat_lit 36))) (SW1 (nat_lit 37)) = true := by
  quickRfl

theorem c8_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 3]
    (SW1 (nat_lit 35))) (SW1 (nat_lit 36)) = true := by
  quickRfl

theorem c8_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 17]
    (SW1 (nat_lit 34))) (SW1 (nat_lit 35)) = true := by
  quickRfl

theorem c8_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 3]
    (SW1 (nat_lit 33))) (SW1 (nat_lit 34)) = true := by
  quickRfl

theorem c8_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 17]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 8))) (SW1 (nat_lit 33)) = true := by
  quickRfl

theorem c8_w : WC (nat_lit 8) = [17, 18] ++ ([19, 17] ++ ([19, 4] ++ ([6, 6] ++ ([3, 6] ++ ([5, 3] ++ ([17, 5] ++ ([19, 3] ++ ([6, 18] ++ ([6, 3] ++ ([18, 18] ++ ([3, 6] ++ ([18, 6] ++ ([4, 5] ++ ([4, 18] ++ ([17, 3] ++ ([19, 3] ++ ([6, 17] ++ ([19, 3] ++ ([6, 17]))))))))))))))))))) := rfl

theorem c8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 8))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 8))) (ST (nat_lit 8)) = true :=
  beq_wordMul_of_eq c8_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c8_p19 c8_p18) c8_p17) c8_p16) c8_p15) c8_p14) c8_p13) c8_p12) c8_p11) c8_p10) c8_p9) c8_p8) c8_p7) c8_p6) c8_p5) c8_p4) c8_p3) c8_p2) c8_p1) c8_p0)

theorem c9_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 4]
    (SW1 (nat_lit 70))) (ST (nat_lit 9)) = true := by
  quickRfl

theorem c9_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 6]
    (SW1 (nat_lit 69))) (SW1 (nat_lit 70)) = true := by
  quickRfl

theorem c9_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 19]
    (SW1 (nat_lit 68))) (SW1 (nat_lit 69)) = true := by
  quickRfl

theorem c9_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 5]
    (SW1 (nat_lit 67))) (SW1 (nat_lit 68)) = true := by
  quickRfl

theorem c9_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 4]
    (SW1 (nat_lit 66))) (SW1 (nat_lit 67)) = true := by
  quickRfl

theorem c9_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 4]
    (SW1 (nat_lit 65))) (SW1 (nat_lit 66)) = true := by
  quickRfl

theorem c9_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 3]
    (SW1 (nat_lit 64))) (SW1 (nat_lit 65)) = true := by
  quickRfl

theorem c9_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 5]
    (SW1 (nat_lit 63))) (SW1 (nat_lit 64)) = true := by
  quickRfl

theorem c9_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 5]
    (SW1 (nat_lit 62))) (SW1 (nat_lit 63)) = true := by
  quickRfl

theorem c9_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 4]
    (SW1 (nat_lit 61))) (SW1 (nat_lit 62)) = true := by
  quickRfl

theorem c9_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 6]
    (SW1 (nat_lit 60))) (SW1 (nat_lit 61)) = true := by
  quickRfl

theorem c9_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 17]
    (SW1 (nat_lit 59))) (SW1 (nat_lit 60)) = true := by
  quickRfl

theorem c9_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 18]
    (SW1 (nat_lit 58))) (SW1 (nat_lit 59)) = true := by
  quickRfl

theorem c9_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 5]
    (SW1 (nat_lit 57))) (SW1 (nat_lit 58)) = true := by
  quickRfl

theorem c9_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 5]
    (SW1 (nat_lit 56))) (SW1 (nat_lit 57)) = true := by
  quickRfl

theorem c9_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 18]
    (SW1 (nat_lit 55))) (SW1 (nat_lit 56)) = true := by
  quickRfl

theorem c9_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 3]
    (SW1 (nat_lit 54))) (SW1 (nat_lit 55)) = true := by
  quickRfl

theorem c9_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 4]
    (SW1 (nat_lit 53))) (SW1 (nat_lit 54)) = true := by
  quickRfl

theorem c9_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 3]
    (SW1 (nat_lit 52))) (SW1 (nat_lit 53)) = true := by
  quickRfl

theorem c9_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 3]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 9))) (SW1 (nat_lit 52)) = true := by
  quickRfl

theorem c9_w : WC (nat_lit 9) = [3, 4] ++ ([4, 6] ++ ([17, 19] ++ ([17, 5] ++ ([19, 4] ++ ([19, 4] ++ ([5, 3] ++ ([6, 5] ++ ([3, 5] ++ ([4, 4] ++ ([5, 6] ++ ([5, 17] ++ ([17, 18] ++ ([3, 5] ++ ([4, 5] ++ ([4, 18] ++ ([17, 3] ++ ([5, 4] ++ ([19, 3] ++ ([4, 3]))))))))))))))))))) := rfl

theorem c9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 9))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 9))) (ST (nat_lit 9)) = true :=
  beq_wordMul_of_eq c9_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c9_p19 c9_p18) c9_p17) c9_p16) c9_p15) c9_p14) c9_p13) c9_p12) c9_p11) c9_p10) c9_p9) c9_p8) c9_p7) c9_p6) c9_p5) c9_p4) c9_p3) c9_p2) c9_p1) c9_p0)

end CFSG.KD.Fi24Ext

end
