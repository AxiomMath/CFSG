module

public import Certificates.Kernel.Sporadic.Fi24Ext.Chunks
public import Certificates.Kernel.Sporadic.Fi24Fix.Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree CFSG.KD.Fi24Ext SW12 "Certificates/Kernel/Sporadic/Fi24Ext/data/w12.bin" 152491 4 8387005 15904468432332774563

public section

set_option Elab.async false

open CFSG.KC.Fi24Fix (beq_wordMul_append beq_wordMul_of_eq)

namespace CFSG.KD.Fi24Ext

theorem c48_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [26, 24]
    (SW12 (nat_lit 5))) (ST (nat_lit 48)) = true := by
  quickRfl

theorem c48_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [26, 27]
    (SW12 (nat_lit 4))) (SW12 (nat_lit 5)) = true := by
  quickRfl

theorem c48_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 23]
    (SW12 (nat_lit 3))) (SW12 (nat_lit 4)) = true := by
  quickRfl

theorem c48_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [25, 10]
    (SW12 (nat_lit 2))) (SW12 (nat_lit 3)) = true := by
  quickRfl

theorem c48_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [26, 25]
    (SW12 (nat_lit 1))) (SW12 (nat_lit 2)) = true := by
  quickRfl

theorem c48_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 21]
    (SW12 (nat_lit 0))) (SW12 (nat_lit 1)) = true := by
  quickRfl

theorem c48_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 21]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 48))) (SW12 (nat_lit 0)) = true := by
  quickRfl

theorem c48_w : WC (nat_lit 48) = [26, 24] ++ ([26, 27] ++ ([22, 23] ++ ([25, 10] ++ ([26, 25] ++ ([23, 21] ++ ([23, 21])))))) := rfl

theorem c48 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 48))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 48))) (ST (nat_lit 48)) = true :=
  beq_wordMul_of_eq c48_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c48_p6 c48_p5) c48_p4) c48_p3) c48_p2) c48_p1) c48_p0)

theorem c49_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 6]
    (SW12 (nat_lit 15))) (ST (nat_lit 49)) = true := by
  quickRfl

theorem c49_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [10, 28]
    (SW12 (nat_lit 14))) (SW12 (nat_lit 15)) = true := by
  quickRfl

theorem c49_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [11, 5]
    (SW12 (nat_lit 13))) (SW12 (nat_lit 14)) = true := by
  quickRfl

theorem c49_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [25, 20]
    (SW12 (nat_lit 12))) (SW12 (nat_lit 13)) = true := by
  quickRfl

theorem c49_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 23]
    (SW12 (nat_lit 11))) (SW12 (nat_lit 12)) = true := by
  quickRfl

theorem c49_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 7]
    (SW12 (nat_lit 10))) (SW12 (nat_lit 11)) = true := by
  quickRfl

theorem c49_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [14, 23]
    (SW12 (nat_lit 9))) (SW12 (nat_lit 10)) = true := by
  quickRfl

theorem c49_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 23]
    (SW12 (nat_lit 8))) (SW12 (nat_lit 9)) = true := by
  quickRfl

theorem c49_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [15, 10]
    (SW12 (nat_lit 7))) (SW12 (nat_lit 8)) = true := by
  quickRfl

theorem c49_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 27]
    (SW12 (nat_lit 6))) (SW12 (nat_lit 7)) = true := by
  quickRfl

theorem c49_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [15, 25]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 49))) (SW12 (nat_lit 6)) = true := by
  quickRfl

theorem c49_w : WC (nat_lit 49) = [3, 6] ++ ([10, 28] ++ ([11, 5] ++ ([25, 20] ++ ([20, 23] ++ ([7, 7] ++ ([14, 23] ++ ([23, 23] ++ ([15, 10] ++ ([9, 27] ++ ([15, 25])))))))))) := rfl

theorem c49 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 49))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 49))) (ST (nat_lit 49)) = true :=
  beq_wordMul_of_eq c49_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c49_p10 c49_p9) c49_p8) c49_p7) c49_p6) c49_p5) c49_p4) c49_p3) c49_p2) c49_p1) c49_p0)

theorem c50_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 11]
    (SW12 (nat_lit 27))) (ST (nat_lit 50)) = true := by
  quickRfl

theorem c50_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 18]
    (SW12 (nat_lit 26))) (SW12 (nat_lit 27)) = true := by
  quickRfl

theorem c50_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 21]
    (SW12 (nat_lit 25))) (SW12 (nat_lit 26)) = true := by
  quickRfl

theorem c50_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 13]
    (SW12 (nat_lit 24))) (SW12 (nat_lit 25)) = true := by
  quickRfl

theorem c50_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 22]
    (SW12 (nat_lit 23))) (SW12 (nat_lit 24)) = true := by
  quickRfl

theorem c50_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 28]
    (SW12 (nat_lit 22))) (SW12 (nat_lit 23)) = true := by
  quickRfl

theorem c50_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [13, 12]
    (SW12 (nat_lit 21))) (SW12 (nat_lit 22)) = true := by
  quickRfl

theorem c50_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 9]
    (SW12 (nat_lit 20))) (SW12 (nat_lit 21)) = true := by
  quickRfl

theorem c50_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 22]
    (SW12 (nat_lit 19))) (SW12 (nat_lit 20)) = true := by
  quickRfl

theorem c50_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [10, 26]
    (SW12 (nat_lit 18))) (SW12 (nat_lit 19)) = true := by
  quickRfl

theorem c50_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [10, 11]
    (SW12 (nat_lit 17))) (SW12 (nat_lit 18)) = true := by
  quickRfl

theorem c50_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [26, 15]
    (SW12 (nat_lit 16))) (SW12 (nat_lit 17)) = true := by
  quickRfl

theorem c50_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [11, 15]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 50))) (SW12 (nat_lit 16)) = true := by
  quickRfl

theorem c50_w : WC (nat_lit 50) = [5, 11] ++ ([9, 18] ++ ([4, 21] ++ ([21, 13] ++ ([6, 22] ++ ([20, 28] ++ ([13, 12] ++ ([7, 9] ++ ([23, 22] ++ ([10, 26] ++ ([10, 11] ++ ([26, 15] ++ ([11, 15])))))))))))) := rfl

theorem c50 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 50))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 50))) (ST (nat_lit 50)) = true :=
  beq_wordMul_of_eq c50_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c50_p12 c50_p11) c50_p10) c50_p9) c50_p8) c50_p7) c50_p6) c50_p5) c50_p4) c50_p3) c50_p2) c50_p1) c50_p0)

theorem c51_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 28]
    (SW12 (nat_lit 36))) (ST (nat_lit 51)) = true := by
  quickRfl

theorem c51_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [10, 9]
    (SW12 (nat_lit 35))) (SW12 (nat_lit 36)) = true := by
  quickRfl

theorem c51_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 5]
    (SW12 (nat_lit 34))) (SW12 (nat_lit 35)) = true := by
  quickRfl

theorem c51_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 15]
    (SW12 (nat_lit 33))) (SW12 (nat_lit 34)) = true := by
  quickRfl

theorem c51_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 7]
    (SW12 (nat_lit 32))) (SW12 (nat_lit 33)) = true := by
  quickRfl

theorem c51_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [27, 15]
    (SW12 (nat_lit 31))) (SW12 (nat_lit 32)) = true := by
  quickRfl

theorem c51_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 18]
    (SW12 (nat_lit 30))) (SW12 (nat_lit 31)) = true := by
  quickRfl

theorem c51_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [27, 13]
    (SW12 (nat_lit 29))) (SW12 (nat_lit 30)) = true := by
  quickRfl

theorem c51_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [12, 21]
    (SW12 (nat_lit 28))) (SW12 (nat_lit 29)) = true := by
  quickRfl

theorem c51_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 15]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 51))) (SW12 (nat_lit 28)) = true := by
  quickRfl

theorem c51_w : WC (nat_lit 51) = [21, 28] ++ ([10, 9] ++ ([7, 5] ++ ([8, 15] ++ ([21, 7] ++ ([27, 15] ++ ([9, 18] ++ ([27, 13] ++ ([12, 21] ++ ([18, 15]))))))))) := rfl

theorem c51 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 51))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 51))) (ST (nat_lit 51)) = true :=
  beq_wordMul_of_eq c51_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c51_p9 c51_p8) c51_p7) c51_p6) c51_p5) c51_p4) c51_p3) c51_p2) c51_p1) c51_p0)

theorem c52_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [25, 21]
    (SW12 (nat_lit 45))) (ST (nat_lit 52)) = true := by
  quickRfl

theorem c52_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 6]
    (SW12 (nat_lit 44))) (SW12 (nat_lit 45)) = true := by
  quickRfl

theorem c52_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 10]
    (SW12 (nat_lit 43))) (SW12 (nat_lit 44)) = true := by
  quickRfl

theorem c52_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 18]
    (SW12 (nat_lit 42))) (SW12 (nat_lit 43)) = true := by
  quickRfl

theorem c52_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 10]
    (SW12 (nat_lit 41))) (SW12 (nat_lit 42)) = true := by
  quickRfl

theorem c52_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [24, 14]
    (SW12 (nat_lit 40))) (SW12 (nat_lit 41)) = true := by
  quickRfl

theorem c52_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [13, 7]
    (SW12 (nat_lit 39))) (SW12 (nat_lit 40)) = true := by
  quickRfl

theorem c52_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [25, 15]
    (SW12 (nat_lit 38))) (SW12 (nat_lit 39)) = true := by
  quickRfl

theorem c52_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 8]
    (SW12 (nat_lit 37))) (SW12 (nat_lit 38)) = true := by
  quickRfl

theorem c52_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [26, 21]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 52))) (SW12 (nat_lit 37)) = true := by
  quickRfl

theorem c52_w : WC (nat_lit 52) = [25, 21] ++ ([23, 6] ++ ([22, 10] ++ ([9, 18] ++ ([23, 10] ++ ([24, 14] ++ ([13, 7] ++ ([25, 15] ++ ([18, 8] ++ ([26, 21]))))))))) := rfl

theorem c52 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 52))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 52))) (ST (nat_lit 52)) = true :=
  beq_wordMul_of_eq c52_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c52_p9 c52_p8) c52_p7) c52_p6) c52_p5) c52_p4) c52_p3) c52_p2) c52_p1) c52_p0)

theorem c53_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [25, 13]
    (SW12 (nat_lit 54))) (ST (nat_lit 53)) = true := by
  quickRfl

theorem c53_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [15, 14]
    (SW12 (nat_lit 53))) (SW12 (nat_lit 54)) = true := by
  quickRfl

theorem c53_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 19]
    (SW12 (nat_lit 52))) (SW12 (nat_lit 53)) = true := by
  quickRfl

theorem c53_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [14, 20]
    (SW12 (nat_lit 51))) (SW12 (nat_lit 52)) = true := by
  quickRfl

theorem c53_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [24, 18]
    (SW12 (nat_lit 50))) (SW12 (nat_lit 51)) = true := by
  quickRfl

theorem c53_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 6]
    (SW12 (nat_lit 49))) (SW12 (nat_lit 50)) = true := by
  quickRfl

theorem c53_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 23]
    (SW12 (nat_lit 48))) (SW12 (nat_lit 49)) = true := by
  quickRfl

theorem c53_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [12, 10]
    (SW12 (nat_lit 47))) (SW12 (nat_lit 48)) = true := by
  quickRfl

theorem c53_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [28, 15]
    (SW12 (nat_lit 46))) (SW12 (nat_lit 47)) = true := by
  quickRfl

theorem c53_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 13]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 53))) (SW12 (nat_lit 46)) = true := by
  quickRfl

theorem c53_w : WC (nat_lit 53) = [25, 13] ++ ([15, 14] ++ ([22, 19] ++ ([14, 20] ++ ([24, 18] ++ ([23, 6] ++ ([18, 23] ++ ([12, 10] ++ ([28, 15] ++ ([8, 13]))))))))) := rfl

theorem c53 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 53))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 53))) (ST (nat_lit 53)) = true :=
  beq_wordMul_of_eq c53_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c53_p9 c53_p8) c53_p7) c53_p6) c53_p5) c53_p4) c53_p3) c53_p2) c53_p1) c53_p0)

end CFSG.KD.Fi24Ext

end
