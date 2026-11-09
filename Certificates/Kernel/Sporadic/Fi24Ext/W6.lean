module

public import Certificates.Kernel.Sporadic.Fi24Ext.Chunks
public import Certificates.Kernel.Sporadic.Fi24Fix.Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree CFSG.KD.Fi24Ext SW6 "Certificates/Kernel/Sporadic/Fi24Ext/data/w6.bin" 152491 4 9911915 2336366509081209381

public section

set_option Elab.async false

open CFSG.KC.Fi24Fix (beq_wordMul_append beq_wordMul_of_eq)

namespace CFSG.KD.Fi24Ext

theorem c26_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 18]
    (SW6 (nat_lit 18))) (ST (nat_lit 26)) = true := by
  quickRfl

theorem c26_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 23]
    (SW6 (nat_lit 17))) (SW6 (nat_lit 18)) = true := by
  quickRfl

theorem c26_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 7]
    (SW6 (nat_lit 16))) (SW6 (nat_lit 17)) = true := by
  quickRfl

theorem c26_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 4]
    (SW6 (nat_lit 15))) (SW6 (nat_lit 16)) = true := by
  quickRfl

theorem c26_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 6]
    (SW6 (nat_lit 14))) (SW6 (nat_lit 15)) = true := by
  quickRfl

theorem c26_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 10]
    (SW6 (nat_lit 13))) (SW6 (nat_lit 14)) = true := by
  quickRfl

theorem c26_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 6]
    (SW6 (nat_lit 12))) (SW6 (nat_lit 13)) = true := by
  quickRfl

theorem c26_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 6]
    (SW6 (nat_lit 11))) (SW6 (nat_lit 12)) = true := by
  quickRfl

theorem c26_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 3]
    (SW6 (nat_lit 10))) (SW6 (nat_lit 11)) = true := by
  quickRfl

theorem c26_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 23]
    (SW6 (nat_lit 9))) (SW6 (nat_lit 10)) = true := by
  quickRfl

theorem c26_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 7]
    (SW6 (nat_lit 8))) (SW6 (nat_lit 9)) = true := by
  quickRfl

theorem c26_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 6]
    (SW6 (nat_lit 7))) (SW6 (nat_lit 8)) = true := by
  quickRfl

theorem c26_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 18]
    (SW6 (nat_lit 6))) (SW6 (nat_lit 7)) = true := by
  quickRfl

theorem c26_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 8]
    (SW6 (nat_lit 5))) (SW6 (nat_lit 6)) = true := by
  quickRfl

theorem c26_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 20]
    (SW6 (nat_lit 4))) (SW6 (nat_lit 5)) = true := by
  quickRfl

theorem c26_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 22]
    (SW6 (nat_lit 3))) (SW6 (nat_lit 4)) = true := by
  quickRfl

theorem c26_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 23]
    (SW6 (nat_lit 2))) (SW6 (nat_lit 3)) = true := by
  quickRfl

theorem c26_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 23]
    (SW6 (nat_lit 1))) (SW6 (nat_lit 2)) = true := by
  quickRfl

theorem c26_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 5]
    (SW6 (nat_lit 0))) (SW6 (nat_lit 1)) = true := by
  quickRfl

theorem c26_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 20]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 26))) (SW6 (nat_lit 0)) = true := by
  quickRfl

theorem c26_w : WC (nat_lit 26) = [7, 18] ++ ([6, 23] ++ ([18, 7] ++ ([23, 4] ++ ([21, 6] ++ ([20, 10] ++ ([4, 6] ++ ([5, 6] ++ ([9, 3] ++ ([20, 23] ++ ([23, 7] ++ ([21, 6] ++ ([8, 18] ++ ([9, 8] ++ ([3, 20] ++ ([20, 22] ++ ([7, 23] ++ ([6, 23] ++ ([8, 5] ++ ([6, 20]))))))))))))))))))) := rfl

theorem c26 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 26))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 26))) (ST (nat_lit 26)) = true :=
  beq_wordMul_of_eq c26_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c26_p19 c26_p18) c26_p17) c26_p16) c26_p15) c26_p14) c26_p13) c26_p12) c26_p11) c26_p10) c26_p9) c26_p8) c26_p7) c26_p6) c26_p5) c26_p4) c26_p3) c26_p2) c26_p1) c26_p0)

theorem c27_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 22]
    (SW6 (nat_lit 37))) (ST (nat_lit 27)) = true := by
  quickRfl

theorem c27_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 9]
    (SW6 (nat_lit 36))) (SW6 (nat_lit 37)) = true := by
  quickRfl

theorem c27_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 21]
    (SW6 (nat_lit 35))) (SW6 (nat_lit 36)) = true := by
  quickRfl

theorem c27_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 23]
    (SW6 (nat_lit 34))) (SW6 (nat_lit 35)) = true := by
  quickRfl

theorem c27_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 8]
    (SW6 (nat_lit 33))) (SW6 (nat_lit 34)) = true := by
  quickRfl

theorem c27_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 23]
    (SW6 (nat_lit 32))) (SW6 (nat_lit 33)) = true := by
  quickRfl

theorem c27_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 19]
    (SW6 (nat_lit 31))) (SW6 (nat_lit 32)) = true := by
  quickRfl

theorem c27_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 4]
    (SW6 (nat_lit 30))) (SW6 (nat_lit 31)) = true := by
  quickRfl

theorem c27_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 5]
    (SW6 (nat_lit 29))) (SW6 (nat_lit 30)) = true := by
  quickRfl

theorem c27_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 8]
    (SW6 (nat_lit 28))) (SW6 (nat_lit 29)) = true := by
  quickRfl

theorem c27_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 19]
    (SW6 (nat_lit 27))) (SW6 (nat_lit 28)) = true := by
  quickRfl

theorem c27_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 6]
    (SW6 (nat_lit 26))) (SW6 (nat_lit 27)) = true := by
  quickRfl

theorem c27_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 5]
    (SW6 (nat_lit 25))) (SW6 (nat_lit 26)) = true := by
  quickRfl

theorem c27_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 8]
    (SW6 (nat_lit 24))) (SW6 (nat_lit 25)) = true := by
  quickRfl

theorem c27_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [10, 19]
    (SW6 (nat_lit 23))) (SW6 (nat_lit 24)) = true := by
  quickRfl

theorem c27_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 10]
    (SW6 (nat_lit 22))) (SW6 (nat_lit 23)) = true := by
  quickRfl

theorem c27_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 23]
    (SW6 (nat_lit 21))) (SW6 (nat_lit 22)) = true := by
  quickRfl

theorem c27_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 3]
    (SW6 (nat_lit 20))) (SW6 (nat_lit 21)) = true := by
  quickRfl

theorem c27_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 3]
    (SW6 (nat_lit 19))) (SW6 (nat_lit 20)) = true := by
  quickRfl

theorem c27_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 18]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 27))) (SW6 (nat_lit 19)) = true := by
  quickRfl

theorem c27_w : WC (nat_lit 27) = [18, 22] ++ ([8, 9] ++ ([5, 21] ++ ([3, 23] ++ ([4, 8] ++ ([8, 23] ++ ([4, 19] ++ ([23, 4] ++ ([8, 5] ++ ([22, 8] ++ ([4, 19] ++ ([8, 6] ++ ([20, 5] ++ ([20, 8] ++ ([10, 19] ++ ([18, 10] ++ ([19, 23] ++ ([21, 3] ++ ([21, 3] ++ ([19, 18]))))))))))))))))))) := rfl

theorem c27 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 27))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 27))) (ST (nat_lit 27)) = true :=
  beq_wordMul_of_eq c27_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c27_p19 c27_p18) c27_p17) c27_p16) c27_p15) c27_p14) c27_p13) c27_p12) c27_p11) c27_p10) c27_p9) c27_p8) c27_p7) c27_p6) c27_p5) c27_p4) c27_p3) c27_p2) c27_p1) c27_p0)

theorem c28_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 23]
    (SW6 (nat_lit 45))) (ST (nat_lit 28)) = true := by
  quickRfl

theorem c28_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 23]
    (SW6 (nat_lit 44))) (SW6 (nat_lit 45)) = true := by
  quickRfl

theorem c28_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 22]
    (SW6 (nat_lit 43))) (SW6 (nat_lit 44)) = true := by
  quickRfl

theorem c28_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 9]
    (SW6 (nat_lit 42))) (SW6 (nat_lit 43)) = true := by
  quickRfl

theorem c28_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 22]
    (SW6 (nat_lit 41))) (SW6 (nat_lit 42)) = true := by
  quickRfl

theorem c28_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 20]
    (SW6 (nat_lit 40))) (SW6 (nat_lit 41)) = true := by
  quickRfl

theorem c28_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 9]
    (SW6 (nat_lit 39))) (SW6 (nat_lit 40)) = true := by
  quickRfl

theorem c28_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 21]
    (SW6 (nat_lit 38))) (SW6 (nat_lit 39)) = true := by
  quickRfl

theorem c28_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 20]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 28))) (SW6 (nat_lit 38)) = true := by
  quickRfl

theorem c28_w : WC (nat_lit 28) = [22, 23] ++ ([22, 23] ++ ([22, 22] ++ ([23, 9] ++ ([23, 22] ++ ([23, 20] ++ ([20, 9] ++ ([23, 21] ++ ([21, 20])))))))) := rfl

theorem c28 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 28))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 28))) (ST (nat_lit 28)) = true :=
  beq_wordMul_of_eq c28_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c28_p8 c28_p7) c28_p6) c28_p5) c28_p4) c28_p3) c28_p2) c28_p1) c28_p0)

theorem c29_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 22]
    (SW6 (nat_lit 64))) (ST (nat_lit 29)) = true := by
  quickRfl

theorem c29_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 19]
    (SW6 (nat_lit 63))) (SW6 (nat_lit 64)) = true := by
  quickRfl

theorem c29_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 17]
    (SW6 (nat_lit 62))) (SW6 (nat_lit 63)) = true := by
  quickRfl

theorem c29_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 3]
    (SW6 (nat_lit 61))) (SW6 (nat_lit 62)) = true := by
  quickRfl

theorem c29_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 6]
    (SW6 (nat_lit 60))) (SW6 (nat_lit 61)) = true := by
  quickRfl

theorem c29_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [11, 5]
    (SW6 (nat_lit 59))) (SW6 (nat_lit 60)) = true := by
  quickRfl

theorem c29_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 4]
    (SW6 (nat_lit 58))) (SW6 (nat_lit 59)) = true := by
  quickRfl

theorem c29_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 21]
    (SW6 (nat_lit 57))) (SW6 (nat_lit 58)) = true := by
  quickRfl

theorem c29_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 23]
    (SW6 (nat_lit 56))) (SW6 (nat_lit 57)) = true := by
  quickRfl

theorem c29_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 19]
    (SW6 (nat_lit 55))) (SW6 (nat_lit 56)) = true := by
  quickRfl

theorem c29_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 19]
    (SW6 (nat_lit 54))) (SW6 (nat_lit 55)) = true := by
  quickRfl

theorem c29_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 22]
    (SW6 (nat_lit 53))) (SW6 (nat_lit 54)) = true := by
  quickRfl

theorem c29_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 9]
    (SW6 (nat_lit 52))) (SW6 (nat_lit 53)) = true := by
  quickRfl

theorem c29_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 17]
    (SW6 (nat_lit 51))) (SW6 (nat_lit 52)) = true := by
  quickRfl

theorem c29_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 18]
    (SW6 (nat_lit 50))) (SW6 (nat_lit 51)) = true := by
  quickRfl

theorem c29_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 21]
    (SW6 (nat_lit 49))) (SW6 (nat_lit 50)) = true := by
  quickRfl

theorem c29_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 5]
    (SW6 (nat_lit 48))) (SW6 (nat_lit 49)) = true := by
  quickRfl

theorem c29_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 11]
    (SW6 (nat_lit 47))) (SW6 (nat_lit 48)) = true := by
  quickRfl

theorem c29_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 18]
    (SW6 (nat_lit 46))) (SW6 (nat_lit 47)) = true := by
  quickRfl

theorem c29_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [24, 23]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 29))) (SW6 (nat_lit 46)) = true := by
  quickRfl

theorem c29_w : WC (nat_lit 29) = [22, 22] ++ ([22, 19] ++ ([8, 17] ++ ([19, 3] ++ ([22, 6] ++ ([11, 5] ++ ([6, 4] ++ ([20, 21] ++ ([18, 23] ++ ([3, 19] ++ ([3, 19] ++ ([19, 22] ++ ([6, 9] ++ ([6, 17] ++ ([20, 18] ++ ([4, 21] ++ ([17, 5] ++ ([21, 11] ++ ([6, 18] ++ ([24, 23]))))))))))))))))))) := rfl

theorem c29 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 29))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 29))) (ST (nat_lit 29)) = true :=
  beq_wordMul_of_eq c29_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c29_p19 c29_p18) c29_p17) c29_p16) c29_p15) c29_p14) c29_p13) c29_p12) c29_p11) c29_p10) c29_p9) c29_p8) c29_p7) c29_p6) c29_p5) c29_p4) c29_p3) c29_p2) c29_p1) c29_p0)

end CFSG.KD.Fi24Ext

end
