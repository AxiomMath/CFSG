module

public import Certificates.Kernel.Sporadic.Fi24Ext.Chunks
public import Certificates.Kernel.Sporadic.Fi24Fix.Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree CFSG.KD.Fi24Ext SW10 "Certificates/Kernel/Sporadic/Fi24Ext/data/w10.bin" 152491 4 9454442 13842787372693849071

public section

set_option Elab.async false

open CFSG.KC.Fi24Fix (beq_wordMul_append beq_wordMul_of_eq)

namespace CFSG.KD.Fi24Ext

theorem c41_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 8]
    (SW10 (nat_lit 18))) (ST (nat_lit 41)) = true := by
  quickRfl

theorem c41_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [26, 3]
    (SW10 (nat_lit 17))) (SW10 (nat_lit 18)) = true := by
  quickRfl

theorem c41_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 20]
    (SW10 (nat_lit 16))) (SW10 (nat_lit 17)) = true := by
  quickRfl

theorem c41_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 24]
    (SW10 (nat_lit 15))) (SW10 (nat_lit 16)) = true := by
  quickRfl

theorem c41_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 9]
    (SW10 (nat_lit 14))) (SW10 (nat_lit 15)) = true := by
  quickRfl

theorem c41_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [13, 7]
    (SW10 (nat_lit 13))) (SW10 (nat_lit 14)) = true := by
  quickRfl

theorem c41_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [24, 24]
    (SW10 (nat_lit 12))) (SW10 (nat_lit 13)) = true := by
  quickRfl

theorem c41_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 7]
    (SW10 (nat_lit 11))) (SW10 (nat_lit 12)) = true := by
  quickRfl

theorem c41_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 25]
    (SW10 (nat_lit 10))) (SW10 (nat_lit 11)) = true := by
  quickRfl

theorem c41_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 3]
    (SW10 (nat_lit 9))) (SW10 (nat_lit 10)) = true := by
  quickRfl

theorem c41_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 5]
    (SW10 (nat_lit 8))) (SW10 (nat_lit 9)) = true := by
  quickRfl

theorem c41_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 9]
    (SW10 (nat_lit 7))) (SW10 (nat_lit 8)) = true := by
  quickRfl

theorem c41_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [12, 20]
    (SW10 (nat_lit 6))) (SW10 (nat_lit 7)) = true := by
  quickRfl

theorem c41_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 6]
    (SW10 (nat_lit 5))) (SW10 (nat_lit 6)) = true := by
  quickRfl

theorem c41_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 4]
    (SW10 (nat_lit 4))) (SW10 (nat_lit 5)) = true := by
  quickRfl

theorem c41_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [24, 18]
    (SW10 (nat_lit 3))) (SW10 (nat_lit 4)) = true := by
  quickRfl

theorem c41_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 8]
    (SW10 (nat_lit 2))) (SW10 (nat_lit 3)) = true := by
  quickRfl

theorem c41_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 8]
    (SW10 (nat_lit 1))) (SW10 (nat_lit 2)) = true := by
  quickRfl

theorem c41_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 19]
    (SW10 (nat_lit 0))) (SW10 (nat_lit 1)) = true := by
  quickRfl

theorem c41_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 8]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 41))) (SW10 (nat_lit 0)) = true := by
  quickRfl

theorem c41_w : WC (nat_lit 41) = [6, 8] ++ ([26, 3] ++ ([8, 20] ++ ([3, 24] ++ ([5, 9] ++ ([13, 7] ++ ([24, 24] ++ ([9, 7] ++ ([18, 25] ++ ([19, 3] ++ ([22, 5] ++ ([5, 9] ++ ([12, 20] ++ ([5, 6] ++ ([18, 4] ++ ([24, 18] ++ ([4, 8] ++ ([3, 8] ++ ([5, 19] ++ ([4, 8]))))))))))))))))))) := rfl

theorem c41 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 41))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 41))) (ST (nat_lit 41)) = true :=
  beq_wordMul_of_eq c41_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c41_p19 c41_p18) c41_p17) c41_p16) c41_p15) c41_p14) c41_p13) c41_p12) c41_p11) c41_p10) c41_p9) c41_p8) c41_p7) c41_p6) c41_p5) c41_p4) c41_p3) c41_p2) c41_p1) c41_p0)

theorem c42_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [12, 18]
    (SW10 (nat_lit 37))) (ST (nat_lit 42)) = true := by
  quickRfl

theorem c42_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 11]
    (SW10 (nat_lit 36))) (SW10 (nat_lit 37)) = true := by
  quickRfl

theorem c42_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [26, 19]
    (SW10 (nat_lit 35))) (SW10 (nat_lit 36)) = true := by
  quickRfl

theorem c42_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 4]
    (SW10 (nat_lit 34))) (SW10 (nat_lit 35)) = true := by
  quickRfl

theorem c42_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [12, 7]
    (SW10 (nat_lit 33))) (SW10 (nat_lit 34)) = true := by
  quickRfl

theorem c42_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 3]
    (SW10 (nat_lit 32))) (SW10 (nat_lit 33)) = true := by
  quickRfl

theorem c42_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [24, 21]
    (SW10 (nat_lit 31))) (SW10 (nat_lit 32)) = true := by
  quickRfl

theorem c42_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 11]
    (SW10 (nat_lit 30))) (SW10 (nat_lit 31)) = true := by
  quickRfl

theorem c42_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 6]
    (SW10 (nat_lit 29))) (SW10 (nat_lit 30)) = true := by
  quickRfl

theorem c42_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 18]
    (SW10 (nat_lit 28))) (SW10 (nat_lit 29)) = true := by
  quickRfl

theorem c42_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 12]
    (SW10 (nat_lit 27))) (SW10 (nat_lit 28)) = true := by
  quickRfl

theorem c42_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 10]
    (SW10 (nat_lit 26))) (SW10 (nat_lit 27)) = true := by
  quickRfl

theorem c42_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [26, 24]
    (SW10 (nat_lit 25))) (SW10 (nat_lit 26)) = true := by
  quickRfl

theorem c42_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [26, 25]
    (SW10 (nat_lit 24))) (SW10 (nat_lit 25)) = true := by
  quickRfl

theorem c42_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [24, 25]
    (SW10 (nat_lit 23))) (SW10 (nat_lit 24)) = true := by
  quickRfl

theorem c42_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 9]
    (SW10 (nat_lit 22))) (SW10 (nat_lit 23)) = true := by
  quickRfl

theorem c42_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 25]
    (SW10 (nat_lit 21))) (SW10 (nat_lit 22)) = true := by
  quickRfl

theorem c42_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 25]
    (SW10 (nat_lit 20))) (SW10 (nat_lit 21)) = true := by
  quickRfl

theorem c42_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 18]
    (SW10 (nat_lit 19))) (SW10 (nat_lit 20)) = true := by
  quickRfl

theorem c42_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [12, 23]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 42))) (SW10 (nat_lit 19)) = true := by
  quickRfl

theorem c42_w : WC (nat_lit 42) = [12, 18] ++ ([21, 11] ++ ([26, 19] ++ ([5, 4] ++ ([12, 7] ++ ([19, 3] ++ ([24, 21] ++ ([17, 11] ++ ([18, 6] ++ ([7, 18] ++ ([18, 12] ++ ([17, 10] ++ ([26, 24] ++ ([26, 25] ++ ([24, 25] ++ ([20, 9] ++ ([7, 25] ++ ([5, 25] ++ ([3, 18] ++ ([12, 23]))))))))))))))))))) := rfl

theorem c42 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 42))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 42))) (ST (nat_lit 42)) = true :=
  beq_wordMul_of_eq c42_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c42_p19 c42_p18) c42_p17) c42_p16) c42_p15) c42_p14) c42_p13) c42_p12) c42_p11) c42_p10) c42_p9) c42_p8) c42_p7) c42_p6) c42_p5) c42_p4) c42_p3) c42_p2) c42_p1) c42_p0)

theorem c43_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22]
    (SW10 (nat_lit 42))) (ST (nat_lit 43)) = true := by
  quickRfl

theorem c43_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [13, 10]
    (SW10 (nat_lit 41))) (SW10 (nat_lit 42)) = true := by
  quickRfl

theorem c43_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [25, 10]
    (SW10 (nat_lit 40))) (SW10 (nat_lit 41)) = true := by
  quickRfl

theorem c43_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [11, 20]
    (SW10 (nat_lit 39))) (SW10 (nat_lit 40)) = true := by
  quickRfl

theorem c43_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 13]
    (SW10 (nat_lit 38))) (SW10 (nat_lit 39)) = true := by
  quickRfl

theorem c43_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 8]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 43))) (SW10 (nat_lit 38)) = true := by
  quickRfl

theorem c43_w : WC (nat_lit 43) = [22] ++ ([13, 10] ++ ([25, 10] ++ ([11, 20] ++ ([20, 13] ++ ([9, 8]))))) := rfl

theorem c43 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 43))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 43))) (ST (nat_lit 43)) = true :=
  beq_wordMul_of_eq c43_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c43_p5 c43_p4) c43_p3) c43_p2) c43_p1) c43_p0)

theorem c44_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 14]
    (SW10 (nat_lit 61))) (ST (nat_lit 44)) = true := by
  quickRfl

theorem c44_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [24, 3]
    (SW10 (nat_lit 60))) (SW10 (nat_lit 61)) = true := by
  quickRfl

theorem c44_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 20]
    (SW10 (nat_lit 59))) (SW10 (nat_lit 60)) = true := by
  quickRfl

theorem c44_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 22]
    (SW10 (nat_lit 58))) (SW10 (nat_lit 59)) = true := by
  quickRfl

theorem c44_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 26]
    (SW10 (nat_lit 57))) (SW10 (nat_lit 58)) = true := by
  quickRfl

theorem c44_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 9]
    (SW10 (nat_lit 56))) (SW10 (nat_lit 57)) = true := by
  quickRfl

theorem c44_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [11, 3]
    (SW10 (nat_lit 55))) (SW10 (nat_lit 56)) = true := by
  quickRfl

theorem c44_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [25, 18]
    (SW10 (nat_lit 54))) (SW10 (nat_lit 55)) = true := by
  quickRfl

theorem c44_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 12]
    (SW10 (nat_lit 53))) (SW10 (nat_lit 54)) = true := by
  quickRfl

theorem c44_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [27, 24]
    (SW10 (nat_lit 52))) (SW10 (nat_lit 53)) = true := by
  quickRfl

theorem c44_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [26, 20]
    (SW10 (nat_lit 51))) (SW10 (nat_lit 52)) = true := by
  quickRfl

theorem c44_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 18]
    (SW10 (nat_lit 50))) (SW10 (nat_lit 51)) = true := by
  quickRfl

theorem c44_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [11, 20]
    (SW10 (nat_lit 49))) (SW10 (nat_lit 50)) = true := by
  quickRfl

theorem c44_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [26, 18]
    (SW10 (nat_lit 48))) (SW10 (nat_lit 49)) = true := by
  quickRfl

theorem c44_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [14, 20]
    (SW10 (nat_lit 47))) (SW10 (nat_lit 48)) = true := by
  quickRfl

theorem c44_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 21]
    (SW10 (nat_lit 46))) (SW10 (nat_lit 47)) = true := by
  quickRfl

theorem c44_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 20]
    (SW10 (nat_lit 45))) (SW10 (nat_lit 46)) = true := by
  quickRfl

theorem c44_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 9]
    (SW10 (nat_lit 44))) (SW10 (nat_lit 45)) = true := by
  quickRfl

theorem c44_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [13, 27]
    (SW10 (nat_lit 43))) (SW10 (nat_lit 44)) = true := by
  quickRfl

theorem c44_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [10, 17]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 44))) (SW10 (nat_lit 43)) = true := by
  quickRfl

theorem c44_w : WC (nat_lit 44) = [17, 14] ++ ([24, 3] ++ ([6, 20] ++ ([18, 22] ++ ([18, 26] ++ ([21, 9] ++ ([11, 3] ++ ([25, 18] ++ ([22, 12] ++ ([27, 24] ++ ([26, 20] ++ ([8, 18] ++ ([11, 20] ++ ([26, 18] ++ ([14, 20] ++ ([3, 21] ++ ([20, 20] ++ ([3, 9] ++ ([13, 27] ++ ([10, 17]))))))))))))))))))) := rfl

theorem c44 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 44))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 44))) (ST (nat_lit 44)) = true :=
  beq_wordMul_of_eq c44_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c44_p19 c44_p18) c44_p17) c44_p16) c44_p15) c44_p14) c44_p13) c44_p12) c44_p11) c44_p10) c44_p9) c44_p8) c44_p7) c44_p6) c44_p5) c44_p4) c44_p3) c44_p2) c44_p1) c44_p0)

end CFSG.KD.Fi24Ext

end
