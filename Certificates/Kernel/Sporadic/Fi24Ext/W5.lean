module

public import Certificates.Kernel.Sporadic.Fi24Ext.Chunks
public import Certificates.Kernel.Sporadic.Fi24Fix.Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree CFSG.KD.Fi24Ext SW5 "Certificates/Kernel/Sporadic/Fi24Ext/data/w5.bin" 152491 4 11436825 1467469342058411571

public section

set_option Elab.async false

open CFSG.KC.Fi24Fix (beq_wordMul_append beq_wordMul_of_eq)

namespace CFSG.KD.Fi24Ext

theorem c22_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 9]
    (SW5 (nat_lit 18))) (ST (nat_lit 22)) = true := by
  quickRfl

theorem c22_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 6]
    (SW5 (nat_lit 17))) (SW5 (nat_lit 18)) = true := by
  quickRfl

theorem c22_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 3]
    (SW5 (nat_lit 16))) (SW5 (nat_lit 17)) = true := by
  quickRfl

theorem c22_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 22]
    (SW5 (nat_lit 15))) (SW5 (nat_lit 16)) = true := by
  quickRfl

theorem c22_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 21]
    (SW5 (nat_lit 14))) (SW5 (nat_lit 15)) = true := by
  quickRfl

theorem c22_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 21]
    (SW5 (nat_lit 13))) (SW5 (nat_lit 14)) = true := by
  quickRfl

theorem c22_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 6]
    (SW5 (nat_lit 12))) (SW5 (nat_lit 13)) = true := by
  quickRfl

theorem c22_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 4]
    (SW5 (nat_lit 11))) (SW5 (nat_lit 12)) = true := by
  quickRfl

theorem c22_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 18]
    (SW5 (nat_lit 10))) (SW5 (nat_lit 11)) = true := by
  quickRfl

theorem c22_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 21]
    (SW5 (nat_lit 9))) (SW5 (nat_lit 10)) = true := by
  quickRfl

theorem c22_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 17]
    (SW5 (nat_lit 8))) (SW5 (nat_lit 9)) = true := by
  quickRfl

theorem c22_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 3]
    (SW5 (nat_lit 7))) (SW5 (nat_lit 8)) = true := by
  quickRfl

theorem c22_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 18]
    (SW5 (nat_lit 6))) (SW5 (nat_lit 7)) = true := by
  quickRfl

theorem c22_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 9]
    (SW5 (nat_lit 5))) (SW5 (nat_lit 6)) = true := by
  quickRfl

theorem c22_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 6]
    (SW5 (nat_lit 4))) (SW5 (nat_lit 5)) = true := by
  quickRfl

theorem c22_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 7]
    (SW5 (nat_lit 3))) (SW5 (nat_lit 4)) = true := by
  quickRfl

theorem c22_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 4]
    (SW5 (nat_lit 2))) (SW5 (nat_lit 3)) = true := by
  quickRfl

theorem c22_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 17]
    (SW5 (nat_lit 1))) (SW5 (nat_lit 2)) = true := by
  quickRfl

theorem c22_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 21]
    (SW5 (nat_lit 0))) (SW5 (nat_lit 1)) = true := by
  quickRfl

theorem c22_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 21]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 22))) (SW5 (nat_lit 0)) = true := by
  quickRfl

theorem c22_w : WC (nat_lit 22) = [9, 9] ++ ([17, 6] ++ ([20, 3] ++ ([6, 22] ++ ([22, 21] ++ ([5, 21] ++ ([20, 6] ++ ([3, 4] ++ ([21, 18] ++ ([20, 21] ++ ([22, 17] ++ ([8, 3] ++ ([19, 18] ++ ([17, 9] ++ ([6, 6] ++ ([4, 7] ++ ([18, 4] ++ ([7, 17] ++ ([17, 21] ++ ([17, 21]))))))))))))))))))) := rfl

theorem c22 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 22))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 22))) (ST (nat_lit 22)) = true :=
  beq_wordMul_of_eq c22_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c22_p19 c22_p18) c22_p17) c22_p16) c22_p15) c22_p14) c22_p13) c22_p12) c22_p11) c22_p10) c22_p9) c22_p8) c22_p7) c22_p6) c22_p5) c22_p4) c22_p3) c22_p2) c22_p1) c22_p0)

theorem c23_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20]
    (SW5 (nat_lit 36))) (ST (nat_lit 23)) = true := by
  quickRfl

theorem c23_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 22]
    (SW5 (nat_lit 35))) (SW5 (nat_lit 36)) = true := by
  quickRfl

theorem c23_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 22]
    (SW5 (nat_lit 34))) (SW5 (nat_lit 35)) = true := by
  quickRfl

theorem c23_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 8]
    (SW5 (nat_lit 33))) (SW5 (nat_lit 34)) = true := by
  quickRfl

theorem c23_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 9]
    (SW5 (nat_lit 32))) (SW5 (nat_lit 33)) = true := by
  quickRfl

theorem c23_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 21]
    (SW5 (nat_lit 31))) (SW5 (nat_lit 32)) = true := by
  quickRfl

theorem c23_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 7]
    (SW5 (nat_lit 30))) (SW5 (nat_lit 31)) = true := by
  quickRfl

theorem c23_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 6]
    (SW5 (nat_lit 29))) (SW5 (nat_lit 30)) = true := by
  quickRfl

theorem c23_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 17]
    (SW5 (nat_lit 28))) (SW5 (nat_lit 29)) = true := by
  quickRfl

theorem c23_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 3]
    (SW5 (nat_lit 27))) (SW5 (nat_lit 28)) = true := by
  quickRfl

theorem c23_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 8]
    (SW5 (nat_lit 26))) (SW5 (nat_lit 27)) = true := by
  quickRfl

theorem c23_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 8]
    (SW5 (nat_lit 25))) (SW5 (nat_lit 26)) = true := by
  quickRfl

theorem c23_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 4]
    (SW5 (nat_lit 24))) (SW5 (nat_lit 25)) = true := by
  quickRfl

theorem c23_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 4]
    (SW5 (nat_lit 23))) (SW5 (nat_lit 24)) = true := by
  quickRfl

theorem c23_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 6]
    (SW5 (nat_lit 22))) (SW5 (nat_lit 23)) = true := by
  quickRfl

theorem c23_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 5]
    (SW5 (nat_lit 21))) (SW5 (nat_lit 22)) = true := by
  quickRfl

theorem c23_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 8]
    (SW5 (nat_lit 20))) (SW5 (nat_lit 21)) = true := by
  quickRfl

theorem c23_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 22]
    (SW5 (nat_lit 19))) (SW5 (nat_lit 20)) = true := by
  quickRfl

theorem c23_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 6]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 23))) (SW5 (nat_lit 19)) = true := by
  quickRfl

theorem c23_w : WC (nat_lit 23) = [20] ++ ([22, 22] ++ ([20, 22] ++ ([8, 8] ++ ([8, 9] ++ ([5, 21] ++ ([19, 7] ++ ([18, 6] ++ ([3, 17] ++ ([8, 3] ++ ([22, 8] ++ ([8, 8] ++ ([3, 4] ++ ([3, 4] ++ ([4, 6] ++ ([3, 5] ++ ([4, 8] ++ ([6, 22] ++ ([17, 6])))))))))))))))))) := rfl

theorem c23 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 23))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 23))) (ST (nat_lit 23)) = true :=
  beq_wordMul_of_eq c23_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c23_p18 c23_p17) c23_p16) c23_p15) c23_p14) c23_p13) c23_p12) c23_p11) c23_p10) c23_p9) c23_p8) c23_p7) c23_p6) c23_p5) c23_p4) c23_p3) c23_p2) c23_p1) c23_p0)

theorem c24_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [10, 22]
    (SW5 (nat_lit 55))) (ST (nat_lit 24)) = true := by
  quickRfl

theorem c24_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [10, 20]
    (SW5 (nat_lit 54))) (SW5 (nat_lit 55)) = true := by
  quickRfl

theorem c24_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 10]
    (SW5 (nat_lit 53))) (SW5 (nat_lit 54)) = true := by
  quickRfl

theorem c24_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 20]
    (SW5 (nat_lit 52))) (SW5 (nat_lit 53)) = true := by
  quickRfl

theorem c24_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 9]
    (SW5 (nat_lit 51))) (SW5 (nat_lit 52)) = true := by
  quickRfl

theorem c24_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 20]
    (SW5 (nat_lit 50))) (SW5 (nat_lit 51)) = true := by
  quickRfl

theorem c24_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 3]
    (SW5 (nat_lit 49))) (SW5 (nat_lit 50)) = true := by
  quickRfl

theorem c24_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 4]
    (SW5 (nat_lit 48))) (SW5 (nat_lit 49)) = true := by
  quickRfl

theorem c24_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 3]
    (SW5 (nat_lit 47))) (SW5 (nat_lit 48)) = true := by
  quickRfl

theorem c24_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 5]
    (SW5 (nat_lit 46))) (SW5 (nat_lit 47)) = true := by
  quickRfl

theorem c24_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 21]
    (SW5 (nat_lit 45))) (SW5 (nat_lit 46)) = true := by
  quickRfl

theorem c24_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 7]
    (SW5 (nat_lit 44))) (SW5 (nat_lit 45)) = true := by
  quickRfl

theorem c24_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 8]
    (SW5 (nat_lit 43))) (SW5 (nat_lit 44)) = true := by
  quickRfl

theorem c24_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 17]
    (SW5 (nat_lit 42))) (SW5 (nat_lit 43)) = true := by
  quickRfl

theorem c24_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 17]
    (SW5 (nat_lit 41))) (SW5 (nat_lit 42)) = true := by
  quickRfl

theorem c24_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 5]
    (SW5 (nat_lit 40))) (SW5 (nat_lit 41)) = true := by
  quickRfl

theorem c24_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [10, 19]
    (SW5 (nat_lit 39))) (SW5 (nat_lit 40)) = true := by
  quickRfl

theorem c24_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 20]
    (SW5 (nat_lit 38))) (SW5 (nat_lit 39)) = true := by
  quickRfl

theorem c24_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 23]
    (SW5 (nat_lit 37))) (SW5 (nat_lit 38)) = true := by
  quickRfl

theorem c24_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 5]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 24))) (SW5 (nat_lit 37)) = true := by
  quickRfl

theorem c24_w : WC (nat_lit 24) = [10, 22] ++ ([10, 20] ++ ([22, 10] ++ ([19, 20] ++ ([9, 9] ++ ([17, 20] ++ ([8, 3] ++ ([18, 4] ++ ([23, 3] ++ ([7, 5] ++ ([19, 21] ++ ([23, 7] ++ ([3, 8] ++ ([19, 17] ++ ([18, 17] ++ ([17, 5] ++ ([10, 19] ++ ([20, 20] ++ ([21, 23] ++ ([21, 5]))))))))))))))))))) := rfl

theorem c24 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 24))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 24))) (ST (nat_lit 24)) = true :=
  beq_wordMul_of_eq c24_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c24_p19 c24_p18) c24_p17) c24_p16) c24_p15) c24_p14) c24_p13) c24_p12) c24_p11) c24_p10) c24_p9) c24_p8) c24_p7) c24_p6) c24_p5) c24_p4) c24_p3) c24_p2) c24_p1) c24_p0)

theorem c25_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 3]
    (SW5 (nat_lit 74))) (ST (nat_lit 25)) = true := by
  quickRfl

theorem c25_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 10]
    (SW5 (nat_lit 73))) (SW5 (nat_lit 74)) = true := by
  quickRfl

theorem c25_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [10, 21]
    (SW5 (nat_lit 72))) (SW5 (nat_lit 73)) = true := by
  quickRfl

theorem c25_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 3]
    (SW5 (nat_lit 71))) (SW5 (nat_lit 72)) = true := by
  quickRfl

theorem c25_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 3]
    (SW5 (nat_lit 70))) (SW5 (nat_lit 71)) = true := by
  quickRfl

theorem c25_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 23]
    (SW5 (nat_lit 69))) (SW5 (nat_lit 70)) = true := by
  quickRfl

theorem c25_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 20]
    (SW5 (nat_lit 68))) (SW5 (nat_lit 69)) = true := by
  quickRfl

theorem c25_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 5]
    (SW5 (nat_lit 67))) (SW5 (nat_lit 68)) = true := by
  quickRfl

theorem c25_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 10]
    (SW5 (nat_lit 66))) (SW5 (nat_lit 67)) = true := by
  quickRfl

theorem c25_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 3]
    (SW5 (nat_lit 65))) (SW5 (nat_lit 66)) = true := by
  quickRfl

theorem c25_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 5]
    (SW5 (nat_lit 64))) (SW5 (nat_lit 65)) = true := by
  quickRfl

theorem c25_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 8]
    (SW5 (nat_lit 63))) (SW5 (nat_lit 64)) = true := by
  quickRfl

theorem c25_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 22]
    (SW5 (nat_lit 62))) (SW5 (nat_lit 63)) = true := by
  quickRfl

theorem c25_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 9]
    (SW5 (nat_lit 61))) (SW5 (nat_lit 62)) = true := by
  quickRfl

theorem c25_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 19]
    (SW5 (nat_lit 60))) (SW5 (nat_lit 61)) = true := by
  quickRfl

theorem c25_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 17]
    (SW5 (nat_lit 59))) (SW5 (nat_lit 60)) = true := by
  quickRfl

theorem c25_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 22]
    (SW5 (nat_lit 58))) (SW5 (nat_lit 59)) = true := by
  quickRfl

theorem c25_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [10, 8]
    (SW5 (nat_lit 57))) (SW5 (nat_lit 58)) = true := by
  quickRfl

theorem c25_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 18]
    (SW5 (nat_lit 56))) (SW5 (nat_lit 57)) = true := by
  quickRfl

theorem c25_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 4]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 25))) (SW5 (nat_lit 56)) = true := by
  quickRfl

theorem c25_w : WC (nat_lit 25) = [21, 3] ++ ([7, 10] ++ ([10, 21] ++ ([23, 3] ++ ([4, 3] ++ ([20, 23] ++ ([18, 20] ++ ([9, 5] ++ ([9, 10] ++ ([22, 3] ++ ([8, 5] ++ ([7, 8] ++ ([6, 22] ++ ([4, 9] ++ ([17, 19] ++ ([7, 17] ++ ([3, 22] ++ ([10, 8] ++ ([23, 18] ++ ([19, 4]))))))))))))))))))) := rfl

theorem c25 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 25))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 25))) (ST (nat_lit 25)) = true :=
  beq_wordMul_of_eq c25_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c25_p19 c25_p18) c25_p17) c25_p16) c25_p15) c25_p14) c25_p13) c25_p12) c25_p11) c25_p10) c25_p9) c25_p8) c25_p7) c25_p6) c25_p5) c25_p4) c25_p3) c25_p2) c25_p1) c25_p0)

end CFSG.KD.Fi24Ext

end
