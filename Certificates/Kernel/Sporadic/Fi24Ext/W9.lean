module

public import Certificates.Kernel.Sporadic.Fi24Ext.Chunks
public import Certificates.Kernel.Sporadic.Fi24Fix.Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree CFSG.KD.Fi24Ext SW9 "Certificates/Kernel/Sporadic/Fi24Ext/data/w9.bin" 152491 4 9149460 14538058475827504221

public section

set_option Elab.async false

open CFSG.KC.Fi24Fix (beq_wordMul_append beq_wordMul_of_eq)

namespace CFSG.KD.Fi24Ext

theorem c37_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 7]
    (SW9 (nat_lit 18))) (ST (nat_lit 37)) = true := by
  quickRfl

theorem c37_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [10, 5]
    (SW9 (nat_lit 17))) (SW9 (nat_lit 18)) = true := by
  quickRfl

theorem c37_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [12, 19]
    (SW9 (nat_lit 16))) (SW9 (nat_lit 17)) = true := by
  quickRfl

theorem c37_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 17]
    (SW9 (nat_lit 15))) (SW9 (nat_lit 16)) = true := by
  quickRfl

theorem c37_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 10]
    (SW9 (nat_lit 14))) (SW9 (nat_lit 15)) = true := by
  quickRfl

theorem c37_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [10, 9]
    (SW9 (nat_lit 13))) (SW9 (nat_lit 14)) = true := by
  quickRfl

theorem c37_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 7]
    (SW9 (nat_lit 12))) (SW9 (nat_lit 13)) = true := by
  quickRfl

theorem c37_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 23]
    (SW9 (nat_lit 11))) (SW9 (nat_lit 12)) = true := by
  quickRfl

theorem c37_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 22]
    (SW9 (nat_lit 10))) (SW9 (nat_lit 11)) = true := by
  quickRfl

theorem c37_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 22]
    (SW9 (nat_lit 9))) (SW9 (nat_lit 10)) = true := by
  quickRfl

theorem c37_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [10, 4]
    (SW9 (nat_lit 8))) (SW9 (nat_lit 9)) = true := by
  quickRfl

theorem c37_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 12]
    (SW9 (nat_lit 7))) (SW9 (nat_lit 8)) = true := by
  quickRfl

theorem c37_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [11, 9]
    (SW9 (nat_lit 6))) (SW9 (nat_lit 7)) = true := by
  quickRfl

theorem c37_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 25]
    (SW9 (nat_lit 5))) (SW9 (nat_lit 6)) = true := by
  quickRfl

theorem c37_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 24]
    (SW9 (nat_lit 4))) (SW9 (nat_lit 5)) = true := by
  quickRfl

theorem c37_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 6]
    (SW9 (nat_lit 3))) (SW9 (nat_lit 4)) = true := by
  quickRfl

theorem c37_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 3]
    (SW9 (nat_lit 2))) (SW9 (nat_lit 3)) = true := by
  quickRfl

theorem c37_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 22]
    (SW9 (nat_lit 1))) (SW9 (nat_lit 2)) = true := by
  quickRfl

theorem c37_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 6]
    (SW9 (nat_lit 0))) (SW9 (nat_lit 1)) = true := by
  quickRfl

theorem c37_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [25, 7]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 37))) (SW9 (nat_lit 0)) = true := by
  quickRfl

theorem c37_w : WC (nat_lit 37) = [8, 7] ++ ([10, 5] ++ ([12, 19] ++ ([21, 17] ++ ([20, 10] ++ ([10, 9] ++ ([7, 7] ++ ([22, 23] ++ ([17, 22] ++ ([5, 22] ++ ([10, 4] ++ ([4, 12] ++ ([11, 9] ++ ([3, 25] ++ ([4, 24] ++ ([17, 6] ++ ([4, 3] ++ ([23, 22] ++ ([4, 6] ++ ([25, 7]))))))))))))))))))) := rfl

theorem c37 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 37))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 37))) (ST (nat_lit 37)) = true :=
  beq_wordMul_of_eq c37_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c37_p19 c37_p18) c37_p17) c37_p16) c37_p15) c37_p14) c37_p13) c37_p12) c37_p11) c37_p10) c37_p9) c37_p8) c37_p7) c37_p6) c37_p5) c37_p4) c37_p3) c37_p2) c37_p1) c37_p0)

theorem c38_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23]
    (SW9 (nat_lit 21))) (ST (nat_lit 38)) = true := by
  quickRfl

theorem c38_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 10]
    (SW9 (nat_lit 20))) (SW9 (nat_lit 21)) = true := by
  quickRfl

theorem c38_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [10, 20]
    (SW9 (nat_lit 19))) (SW9 (nat_lit 20)) = true := by
  quickRfl

theorem c38_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [25, 20]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 38))) (SW9 (nat_lit 19)) = true := by
  quickRfl

theorem c38_w : WC (nat_lit 38) = [23] ++ ([9, 10] ++ ([10, 20] ++ ([25, 20]))) := rfl

theorem c38 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 38))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 38))) (ST (nat_lit 38)) = true :=
  beq_wordMul_of_eq c38_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c38_p3 c38_p2) c38_p1) c38_p0)

theorem c39_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 21]
    (SW9 (nat_lit 40))) (ST (nat_lit 39)) = true := by
  quickRfl

theorem c39_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 25]
    (SW9 (nat_lit 39))) (SW9 (nat_lit 40)) = true := by
  quickRfl

theorem c39_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 4]
    (SW9 (nat_lit 38))) (SW9 (nat_lit 39)) = true := by
  quickRfl

theorem c39_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 8]
    (SW9 (nat_lit 37))) (SW9 (nat_lit 38)) = true := by
  quickRfl

theorem c39_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 24]
    (SW9 (nat_lit 36))) (SW9 (nat_lit 37)) = true := by
  quickRfl

theorem c39_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [26, 21]
    (SW9 (nat_lit 35))) (SW9 (nat_lit 36)) = true := by
  quickRfl

theorem c39_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 6]
    (SW9 (nat_lit 34))) (SW9 (nat_lit 35)) = true := by
  quickRfl

theorem c39_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 10]
    (SW9 (nat_lit 33))) (SW9 (nat_lit 34)) = true := by
  quickRfl

theorem c39_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [13, 11]
    (SW9 (nat_lit 32))) (SW9 (nat_lit 33)) = true := by
  quickRfl

theorem c39_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 10]
    (SW9 (nat_lit 31))) (SW9 (nat_lit 32)) = true := by
  quickRfl

theorem c39_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 5]
    (SW9 (nat_lit 30))) (SW9 (nat_lit 31)) = true := by
  quickRfl

theorem c39_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 12]
    (SW9 (nat_lit 29))) (SW9 (nat_lit 30)) = true := by
  quickRfl

theorem c39_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [24, 21]
    (SW9 (nat_lit 28))) (SW9 (nat_lit 29)) = true := by
  quickRfl

theorem c39_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 10]
    (SW9 (nat_lit 27))) (SW9 (nat_lit 28)) = true := by
  quickRfl

theorem c39_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 18]
    (SW9 (nat_lit 26))) (SW9 (nat_lit 27)) = true := by
  quickRfl

theorem c39_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 17]
    (SW9 (nat_lit 25))) (SW9 (nat_lit 26)) = true := by
  quickRfl

theorem c39_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [24, 21]
    (SW9 (nat_lit 24))) (SW9 (nat_lit 25)) = true := by
  quickRfl

theorem c39_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [11, 25]
    (SW9 (nat_lit 23))) (SW9 (nat_lit 24)) = true := by
  quickRfl

theorem c39_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 12]
    (SW9 (nat_lit 22))) (SW9 (nat_lit 23)) = true := by
  quickRfl

theorem c39_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 24]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 39))) (SW9 (nat_lit 22)) = true := by
  quickRfl

theorem c39_w : WC (nat_lit 39) = [6, 21] ++ ([20, 25] ++ ([21, 4] ++ ([22, 8] ++ ([20, 24] ++ ([26, 21] ++ ([3, 6] ++ ([3, 10] ++ ([13, 11] ++ ([8, 10] ++ ([6, 5] ++ ([23, 12] ++ ([24, 21] ++ ([19, 10] ++ ([7, 18] ++ ([3, 17] ++ ([24, 21] ++ ([11, 25] ++ ([6, 12] ++ ([3, 24]))))))))))))))))))) := rfl

theorem c39 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 39))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 39))) (ST (nat_lit 39)) = true :=
  beq_wordMul_of_eq c39_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c39_p19 c39_p18) c39_p17) c39_p16) c39_p15) c39_p14) c39_p13) c39_p12) c39_p11) c39_p10) c39_p9) c39_p8) c39_p7) c39_p6) c39_p5) c39_p4) c39_p3) c39_p2) c39_p1) c39_p0)

theorem c40_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 10]
    (SW9 (nat_lit 59))) (ST (nat_lit 40)) = true := by
  quickRfl

theorem c40_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 21]
    (SW9 (nat_lit 58))) (SW9 (nat_lit 59)) = true := by
  quickRfl

theorem c40_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 9]
    (SW9 (nat_lit 57))) (SW9 (nat_lit 58)) = true := by
  quickRfl

theorem c40_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [13, 4]
    (SW9 (nat_lit 56))) (SW9 (nat_lit 57)) = true := by
  quickRfl

theorem c40_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 9]
    (SW9 (nat_lit 55))) (SW9 (nat_lit 56)) = true := by
  quickRfl

theorem c40_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 21]
    (SW9 (nat_lit 54))) (SW9 (nat_lit 55)) = true := by
  quickRfl

theorem c40_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 10]
    (SW9 (nat_lit 53))) (SW9 (nat_lit 54)) = true := by
  quickRfl

theorem c40_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 19]
    (SW9 (nat_lit 52))) (SW9 (nat_lit 53)) = true := by
  quickRfl

theorem c40_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [12, 7]
    (SW9 (nat_lit 51))) (SW9 (nat_lit 52)) = true := by
  quickRfl

theorem c40_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [25, 8]
    (SW9 (nat_lit 50))) (SW9 (nat_lit 51)) = true := by
  quickRfl

theorem c40_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 13]
    (SW9 (nat_lit 49))) (SW9 (nat_lit 50)) = true := by
  quickRfl

theorem c40_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 9]
    (SW9 (nat_lit 48))) (SW9 (nat_lit 49)) = true := by
  quickRfl

theorem c40_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 9]
    (SW9 (nat_lit 47))) (SW9 (nat_lit 48)) = true := by
  quickRfl

theorem c40_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 8]
    (SW9 (nat_lit 46))) (SW9 (nat_lit 47)) = true := by
  quickRfl

theorem c40_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 7]
    (SW9 (nat_lit 45))) (SW9 (nat_lit 46)) = true := by
  quickRfl

theorem c40_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [13, 12]
    (SW9 (nat_lit 44))) (SW9 (nat_lit 45)) = true := by
  quickRfl

theorem c40_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 5]
    (SW9 (nat_lit 43))) (SW9 (nat_lit 44)) = true := by
  quickRfl

theorem c40_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 25]
    (SW9 (nat_lit 42))) (SW9 (nat_lit 43)) = true := by
  quickRfl

theorem c40_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [24, 22]
    (SW9 (nat_lit 41))) (SW9 (nat_lit 42)) = true := by
  quickRfl

theorem c40_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 4]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 40))) (SW9 (nat_lit 41)) = true := by
  quickRfl

theorem c40_w : WC (nat_lit 40) = [4, 10] ++ ([4, 21] ++ ([5, 9] ++ ([13, 4] ++ ([3, 9] ++ ([5, 21] ++ ([9, 10] ++ ([19, 19] ++ ([12, 7] ++ ([25, 8] ++ ([22, 13] ++ ([19, 9] ++ ([3, 9] ++ ([19, 8] ++ ([18, 7] ++ ([13, 12] ++ ([3, 5] ++ ([3, 25] ++ ([24, 22] ++ ([7, 4]))))))))))))))))))) := rfl

theorem c40 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 40))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 40))) (ST (nat_lit 40)) = true :=
  beq_wordMul_of_eq c40_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c40_p19 c40_p18) c40_p17) c40_p16) c40_p15) c40_p14) c40_p13) c40_p12) c40_p11) c40_p10) c40_p9) c40_p8) c40_p7) c40_p6) c40_p5) c40_p4) c40_p3) c40_p2) c40_p1) c40_p0)

end CFSG.KD.Fi24Ext

end
