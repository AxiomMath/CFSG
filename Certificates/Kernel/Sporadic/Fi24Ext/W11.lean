module

public import Certificates.Kernel.Sporadic.Fi24Ext.Chunks
public import Certificates.Kernel.Sporadic.Fi24Fix.Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree CFSG.KD.Fi24Ext SW11 "Certificates/Kernel/Sporadic/Fi24Ext/data/w11.bin" 152491 4 8691987 5753233406174171872

public section

set_option Elab.async false

open CFSG.KC.Fi24Fix (beq_wordMul_append beq_wordMul_of_eq)

namespace CFSG.KD.Fi24Ext

theorem c45_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 12]
    (SW11 (nat_lit 18))) (ST (nat_lit 45)) = true := by
  quickRfl

theorem c45_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [10, 4]
    (SW11 (nat_lit 17))) (SW11 (nat_lit 18)) = true := by
  quickRfl

theorem c45_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [10, 3]
    (SW11 (nat_lit 16))) (SW11 (nat_lit 17)) = true := by
  quickRfl

theorem c45_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [13, 3]
    (SW11 (nat_lit 15))) (SW11 (nat_lit 16)) = true := by
  quickRfl

theorem c45_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [14, 13]
    (SW11 (nat_lit 14))) (SW11 (nat_lit 15)) = true := by
  quickRfl

theorem c45_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [14, 20]
    (SW11 (nat_lit 13))) (SW11 (nat_lit 14)) = true := by
  quickRfl

theorem c45_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [10, 17]
    (SW11 (nat_lit 12))) (SW11 (nat_lit 13)) = true := by
  quickRfl

theorem c45_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 17]
    (SW11 (nat_lit 11))) (SW11 (nat_lit 12)) = true := by
  quickRfl

theorem c45_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [12, 22]
    (SW11 (nat_lit 10))) (SW11 (nat_lit 11)) = true := by
  quickRfl

theorem c45_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 22]
    (SW11 (nat_lit 9))) (SW11 (nat_lit 10)) = true := by
  quickRfl

theorem c45_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 21]
    (SW11 (nat_lit 8))) (SW11 (nat_lit 9)) = true := by
  quickRfl

theorem c45_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 21]
    (SW11 (nat_lit 7))) (SW11 (nat_lit 8)) = true := by
  quickRfl

theorem c45_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 7]
    (SW11 (nat_lit 6))) (SW11 (nat_lit 7)) = true := by
  quickRfl

theorem c45_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [25, 8]
    (SW11 (nat_lit 5))) (SW11 (nat_lit 6)) = true := by
  quickRfl

theorem c45_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 19]
    (SW11 (nat_lit 4))) (SW11 (nat_lit 5)) = true := by
  quickRfl

theorem c45_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 19]
    (SW11 (nat_lit 3))) (SW11 (nat_lit 4)) = true := by
  quickRfl

theorem c45_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 10]
    (SW11 (nat_lit 2))) (SW11 (nat_lit 3)) = true := by
  quickRfl

theorem c45_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 12]
    (SW11 (nat_lit 1))) (SW11 (nat_lit 2)) = true := by
  quickRfl

theorem c45_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 14]
    (SW11 (nat_lit 0))) (SW11 (nat_lit 1)) = true := by
  quickRfl

theorem c45_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [10, 13]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 45))) (SW11 (nat_lit 0)) = true := by
  quickRfl

theorem c45_w : WC (nat_lit 45) = [23, 12] ++ ([10, 4] ++ ([10, 3] ++ ([13, 3] ++ ([14, 13] ++ ([14, 20] ++ ([10, 17] ++ ([20, 17] ++ ([12, 22] ++ ([3, 22] ++ ([17, 21] ++ ([19, 21] ++ ([18, 7] ++ ([25, 8] ++ ([3, 19] ++ ([20, 19] ++ ([21, 10] ++ ([7, 12] ++ ([4, 14] ++ ([10, 13]))))))))))))))))))) := rfl

theorem c45 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 45))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 45))) (ST (nat_lit 45)) = true :=
  beq_wordMul_of_eq c45_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c45_p19 c45_p18) c45_p17) c45_p16) c45_p15) c45_p14) c45_p13) c45_p12) c45_p11) c45_p10) c45_p9) c45_p8) c45_p7) c45_p6) c45_p5) c45_p4) c45_p3) c45_p2) c45_p1) c45_p0)

theorem c46_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 22]
    (SW11 (nat_lit 37))) (ST (nat_lit 46)) = true := by
  quickRfl

theorem c46_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 22]
    (SW11 (nat_lit 36))) (SW11 (nat_lit 37)) = true := by
  quickRfl

theorem c46_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [10, 11]
    (SW11 (nat_lit 35))) (SW11 (nat_lit 36)) = true := by
  quickRfl

theorem c46_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 8]
    (SW11 (nat_lit 34))) (SW11 (nat_lit 35)) = true := by
  quickRfl

theorem c46_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 26]
    (SW11 (nat_lit 33))) (SW11 (nat_lit 34)) = true := by
  quickRfl

theorem c46_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 5]
    (SW11 (nat_lit 32))) (SW11 (nat_lit 33)) = true := by
  quickRfl

theorem c46_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [10, 3]
    (SW11 (nat_lit 31))) (SW11 (nat_lit 32)) = true := by
  quickRfl

theorem c46_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 25]
    (SW11 (nat_lit 30))) (SW11 (nat_lit 31)) = true := by
  quickRfl

theorem c46_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 23]
    (SW11 (nat_lit 29))) (SW11 (nat_lit 30)) = true := by
  quickRfl

theorem c46_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 27]
    (SW11 (nat_lit 28))) (SW11 (nat_lit 29)) = true := by
  quickRfl

theorem c46_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 6]
    (SW11 (nat_lit 27))) (SW11 (nat_lit 28)) = true := by
  quickRfl

theorem c46_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 5]
    (SW11 (nat_lit 26))) (SW11 (nat_lit 27)) = true := by
  quickRfl

theorem c46_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [11, 7]
    (SW11 (nat_lit 25))) (SW11 (nat_lit 26)) = true := by
  quickRfl

theorem c46_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 22]
    (SW11 (nat_lit 24))) (SW11 (nat_lit 25)) = true := by
  quickRfl

theorem c46_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 12]
    (SW11 (nat_lit 23))) (SW11 (nat_lit 24)) = true := by
  quickRfl

theorem c46_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 17]
    (SW11 (nat_lit 22))) (SW11 (nat_lit 23)) = true := by
  quickRfl

theorem c46_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 7]
    (SW11 (nat_lit 21))) (SW11 (nat_lit 22)) = true := by
  quickRfl

theorem c46_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 17]
    (SW11 (nat_lit 20))) (SW11 (nat_lit 21)) = true := by
  quickRfl

theorem c46_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 6]
    (SW11 (nat_lit 19))) (SW11 (nat_lit 20)) = true := by
  quickRfl

theorem c46_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 3]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 46))) (SW11 (nat_lit 19)) = true := by
  quickRfl

theorem c46_w : WC (nat_lit 46) = [19, 22] ++ ([8, 22] ++ ([10, 11] ++ ([18, 8] ++ ([3, 26] ++ ([4, 5] ++ ([10, 3] ++ ([23, 25] ++ ([5, 23] ++ ([23, 27] ++ ([6, 6] ++ ([17, 5] ++ ([11, 7] ++ ([22, 22] ++ ([17, 12] ++ ([9, 17] ++ ([9, 7] ++ ([8, 17] ++ ([9, 6] ++ ([7, 3]))))))))))))))))))) := rfl

theorem c46 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 46))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 46))) (ST (nat_lit 46)) = true :=
  beq_wordMul_of_eq c46_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c46_p19 c46_p18) c46_p17) c46_p16) c46_p15) c46_p14) c46_p13) c46_p12) c46_p11) c46_p10) c46_p9) c46_p8) c46_p7) c46_p6) c46_p5) c46_p4) c46_p3) c46_p2) c46_p1) c46_p0)

theorem c47_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [25, 23]
    (SW11 (nat_lit 56))) (ST (nat_lit 47)) = true := by
  quickRfl

theorem c47_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 21]
    (SW11 (nat_lit 55))) (SW11 (nat_lit 56)) = true := by
  quickRfl

theorem c47_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 21]
    (SW11 (nat_lit 54))) (SW11 (nat_lit 55)) = true := by
  quickRfl

theorem c47_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [14, 17]
    (SW11 (nat_lit 53))) (SW11 (nat_lit 54)) = true := by
  quickRfl

theorem c47_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 3]
    (SW11 (nat_lit 52))) (SW11 (nat_lit 53)) = true := by
  quickRfl

theorem c47_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 11]
    (SW11 (nat_lit 51))) (SW11 (nat_lit 52)) = true := by
  quickRfl

theorem c47_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 9]
    (SW11 (nat_lit 50))) (SW11 (nat_lit 51)) = true := by
  quickRfl

theorem c47_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [26, 6]
    (SW11 (nat_lit 49))) (SW11 (nat_lit 50)) = true := by
  quickRfl

theorem c47_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 7]
    (SW11 (nat_lit 48))) (SW11 (nat_lit 49)) = true := by
  quickRfl

theorem c47_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 14]
    (SW11 (nat_lit 47))) (SW11 (nat_lit 48)) = true := by
  quickRfl

theorem c47_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 19]
    (SW11 (nat_lit 46))) (SW11 (nat_lit 47)) = true := by
  quickRfl

theorem c47_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 5]
    (SW11 (nat_lit 45))) (SW11 (nat_lit 46)) = true := by
  quickRfl

theorem c47_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 19]
    (SW11 (nat_lit 44))) (SW11 (nat_lit 45)) = true := by
  quickRfl

theorem c47_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 17]
    (SW11 (nat_lit 43))) (SW11 (nat_lit 44)) = true := by
  quickRfl

theorem c47_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [27, 10]
    (SW11 (nat_lit 42))) (SW11 (nat_lit 43)) = true := by
  quickRfl

theorem c47_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [25, 23]
    (SW11 (nat_lit 41))) (SW11 (nat_lit 42)) = true := by
  quickRfl

theorem c47_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [26, 23]
    (SW11 (nat_lit 40))) (SW11 (nat_lit 41)) = true := by
  quickRfl

theorem c47_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [11, 19]
    (SW11 (nat_lit 39))) (SW11 (nat_lit 40)) = true := by
  quickRfl

theorem c47_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [11, 8]
    (SW11 (nat_lit 38))) (SW11 (nat_lit 39)) = true := by
  quickRfl

theorem c47_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 11]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 47))) (SW11 (nat_lit 38)) = true := by
  quickRfl

theorem c47_w : WC (nat_lit 47) = [25, 23] ++ ([18, 21] ++ ([5, 21] ++ ([14, 17] ++ ([18, 3] ++ ([4, 11] ++ ([7, 9] ++ ([26, 6] ++ ([23, 7] ++ ([3, 14] ++ ([20, 19] ++ ([8, 5] ++ ([3, 19] ++ ([20, 17] ++ ([27, 10] ++ ([25, 23] ++ ([26, 23] ++ ([11, 19] ++ ([11, 8] ++ ([6, 11]))))))))))))))))))) := rfl

theorem c47 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 47))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 47))) (ST (nat_lit 47)) = true :=
  beq_wordMul_of_eq c47_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c47_p19 c47_p18) c47_p17) c47_p16) c47_p15) c47_p14) c47_p13) c47_p12) c47_p11) c47_p10) c47_p9) c47_p8) c47_p7) c47_p6) c47_p5) c47_p4) c47_p3) c47_p2) c47_p1) c47_p0)

end CFSG.KD.Fi24Ext

end
