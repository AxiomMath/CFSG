module

public import Certificates.Kernel.Sporadic.Fi24Ext.Chunks
public import Certificates.Kernel.Sporadic.Fi24Fix.Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree CFSG.KD.Fi24Ext SW8 "Certificates/Kernel/Sporadic/Fi24Ext/data/w8.bin" 152491 4 9606933 6523418890424117159

public section

set_option Elab.async false

open CFSG.KC.Fi24Fix (beq_wordMul_append beq_wordMul_of_eq)

namespace CFSG.KD.Fi24Ext

theorem c33_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 9]
    (SW8 (nat_lit 5))) (ST (nat_lit 33)) = true := by
  quickRfl

theorem c33_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [10, 11]
    (SW8 (nat_lit 4))) (SW8 (nat_lit 5)) = true := by
  quickRfl

theorem c33_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 10]
    (SW8 (nat_lit 3))) (SW8 (nat_lit 4)) = true := by
  quickRfl

theorem c33_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 22]
    (SW8 (nat_lit 2))) (SW8 (nat_lit 3)) = true := by
  quickRfl

theorem c33_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [11, 8]
    (SW8 (nat_lit 1))) (SW8 (nat_lit 2)) = true := by
  quickRfl

theorem c33_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 8]
    (SW8 (nat_lit 0))) (SW8 (nat_lit 1)) = true := by
  quickRfl

theorem c33_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 23]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 33))) (SW8 (nat_lit 0)) = true := by
  quickRfl

theorem c33_w : WC (nat_lit 33) = [9, 9] ++ ([10, 11] ++ ([22, 10] ++ ([20, 22] ++ ([11, 8] ++ ([7, 8] ++ ([18, 23])))))) := rfl

theorem c33 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 33))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 33))) (ST (nat_lit 33)) = true :=
  beq_wordMul_of_eq c33_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c33_p6 c33_p5) c33_p4) c33_p3) c33_p2) c33_p1) c33_p0)

theorem c34_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 17]
    (SW8 (nat_lit 24))) (ST (nat_lit 34)) = true := by
  quickRfl

theorem c34_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 5]
    (SW8 (nat_lit 23))) (SW8 (nat_lit 24)) = true := by
  quickRfl

theorem c34_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 5]
    (SW8 (nat_lit 22))) (SW8 (nat_lit 23)) = true := by
  quickRfl

theorem c34_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 4]
    (SW8 (nat_lit 21))) (SW8 (nat_lit 22)) = true := by
  quickRfl

theorem c34_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 6]
    (SW8 (nat_lit 20))) (SW8 (nat_lit 21)) = true := by
  quickRfl

theorem c34_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 3]
    (SW8 (nat_lit 19))) (SW8 (nat_lit 20)) = true := by
  quickRfl

theorem c34_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 7]
    (SW8 (nat_lit 18))) (SW8 (nat_lit 19)) = true := by
  quickRfl

theorem c34_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 7]
    (SW8 (nat_lit 17))) (SW8 (nat_lit 18)) = true := by
  quickRfl

theorem c34_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 6]
    (SW8 (nat_lit 16))) (SW8 (nat_lit 17)) = true := by
  quickRfl

theorem c34_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 12]
    (SW8 (nat_lit 15))) (SW8 (nat_lit 16)) = true := by
  quickRfl

theorem c34_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 22]
    (SW8 (nat_lit 14))) (SW8 (nat_lit 15)) = true := by
  quickRfl

theorem c34_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 25]
    (SW8 (nat_lit 13))) (SW8 (nat_lit 14)) = true := by
  quickRfl

theorem c34_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 5]
    (SW8 (nat_lit 12))) (SW8 (nat_lit 13)) = true := by
  quickRfl

theorem c34_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [10, 4]
    (SW8 (nat_lit 11))) (SW8 (nat_lit 12)) = true := by
  quickRfl

theorem c34_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 23]
    (SW8 (nat_lit 10))) (SW8 (nat_lit 11)) = true := by
  quickRfl

theorem c34_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 20]
    (SW8 (nat_lit 9))) (SW8 (nat_lit 10)) = true := by
  quickRfl

theorem c34_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 24]
    (SW8 (nat_lit 8))) (SW8 (nat_lit 9)) = true := by
  quickRfl

theorem c34_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 24]
    (SW8 (nat_lit 7))) (SW8 (nat_lit 8)) = true := by
  quickRfl

theorem c34_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 7]
    (SW8 (nat_lit 6))) (SW8 (nat_lit 7)) = true := by
  quickRfl

theorem c34_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 17]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 34))) (SW8 (nat_lit 6)) = true := by
  quickRfl

theorem c34_w : WC (nat_lit 34) = [9, 17] ++ ([21, 5] ++ ([19, 5] ++ ([21, 4] ++ ([5, 6] ++ ([4, 3] ++ ([22, 7] ++ ([21, 7] ++ ([4, 6] ++ ([5, 12] ++ ([8, 22] ++ ([19, 25] ++ ([9, 5] ++ ([10, 4] ++ ([3, 23] ++ ([3, 20] ++ ([4, 24] ++ ([5, 24] ++ ([7, 7] ++ ([18, 17]))))))))))))))))))) := rfl

theorem c34 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 34))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 34))) (ST (nat_lit 34)) = true :=
  beq_wordMul_of_eq c34_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c34_p19 c34_p18) c34_p17) c34_p16) c34_p15) c34_p14) c34_p13) c34_p12) c34_p11) c34_p10) c34_p9) c34_p8) c34_p7) c34_p6) c34_p5) c34_p4) c34_p3) c34_p2) c34_p1) c34_p0)

theorem c35_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 19]
    (SW8 (nat_lit 43))) (ST (nat_lit 35)) = true := by
  quickRfl

theorem c35_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 8]
    (SW8 (nat_lit 42))) (SW8 (nat_lit 43)) = true := by
  quickRfl

theorem c35_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [12, 12]
    (SW8 (nat_lit 41))) (SW8 (nat_lit 42)) = true := by
  quickRfl

theorem c35_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 22]
    (SW8 (nat_lit 40))) (SW8 (nat_lit 41)) = true := by
  quickRfl

theorem c35_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [12, 6]
    (SW8 (nat_lit 39))) (SW8 (nat_lit 40)) = true := by
  quickRfl

theorem c35_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 3]
    (SW8 (nat_lit 38))) (SW8 (nat_lit 39)) = true := by
  quickRfl

theorem c35_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 5]
    (SW8 (nat_lit 37))) (SW8 (nat_lit 38)) = true := by
  quickRfl

theorem c35_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 18]
    (SW8 (nat_lit 36))) (SW8 (nat_lit 37)) = true := by
  quickRfl

theorem c35_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 4]
    (SW8 (nat_lit 35))) (SW8 (nat_lit 36)) = true := by
  quickRfl

theorem c35_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 21]
    (SW8 (nat_lit 34))) (SW8 (nat_lit 35)) = true := by
  quickRfl

theorem c35_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 20]
    (SW8 (nat_lit 33))) (SW8 (nat_lit 34)) = true := by
  quickRfl

theorem c35_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 11]
    (SW8 (nat_lit 32))) (SW8 (nat_lit 33)) = true := by
  quickRfl

theorem c35_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [12, 12]
    (SW8 (nat_lit 31))) (SW8 (nat_lit 32)) = true := by
  quickRfl

theorem c35_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [12, 21]
    (SW8 (nat_lit 30))) (SW8 (nat_lit 31)) = true := by
  quickRfl

theorem c35_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 9]
    (SW8 (nat_lit 29))) (SW8 (nat_lit 30)) = true := by
  quickRfl

theorem c35_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [24, 25]
    (SW8 (nat_lit 28))) (SW8 (nat_lit 29)) = true := by
  quickRfl

theorem c35_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 10]
    (SW8 (nat_lit 27))) (SW8 (nat_lit 28)) = true := by
  quickRfl

theorem c35_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [24, 3]
    (SW8 (nat_lit 26))) (SW8 (nat_lit 27)) = true := by
  quickRfl

theorem c35_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 23]
    (SW8 (nat_lit 25))) (SW8 (nat_lit 26)) = true := by
  quickRfl

theorem c35_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 20]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 35))) (SW8 (nat_lit 25)) = true := by
  quickRfl

theorem c35_w : WC (nat_lit 35) = [20, 19] ++ ([8, 8] ++ ([12, 12] ++ ([22, 22] ++ ([12, 6] ++ ([8, 3] ++ ([6, 5] ++ ([9, 18] ++ ([3, 4] ++ ([5, 21] ++ ([3, 20] ++ ([18, 11] ++ ([12, 12] ++ ([12, 21] ++ ([20, 9] ++ ([24, 25] ++ ([7, 10] ++ ([24, 3] ++ ([9, 23] ++ ([17, 20]))))))))))))))))))) := rfl

theorem c35 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 35))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 35))) (ST (nat_lit 35)) = true :=
  beq_wordMul_of_eq c35_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c35_p19 c35_p18) c35_p17) c35_p16) c35_p15) c35_p14) c35_p13) c35_p12) c35_p11) c35_p10) c35_p9) c35_p8) c35_p7) c35_p6) c35_p5) c35_p4) c35_p3) c35_p2) c35_p1) c35_p0)

theorem c36_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 21]
    (SW8 (nat_lit 62))) (ST (nat_lit 36)) = true := by
  quickRfl

theorem c36_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 21]
    (SW8 (nat_lit 61))) (SW8 (nat_lit 62)) = true := by
  quickRfl

theorem c36_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 24]
    (SW8 (nat_lit 60))) (SW8 (nat_lit 61)) = true := by
  quickRfl

theorem c36_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 10]
    (SW8 (nat_lit 59))) (SW8 (nat_lit 60)) = true := by
  quickRfl

theorem c36_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [12, 3]
    (SW8 (nat_lit 58))) (SW8 (nat_lit 59)) = true := by
  quickRfl

theorem c36_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 24]
    (SW8 (nat_lit 57))) (SW8 (nat_lit 58)) = true := by
  quickRfl

theorem c36_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 8]
    (SW8 (nat_lit 56))) (SW8 (nat_lit 57)) = true := by
  quickRfl

theorem c36_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 19]
    (SW8 (nat_lit 55))) (SW8 (nat_lit 56)) = true := by
  quickRfl

theorem c36_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 18]
    (SW8 (nat_lit 54))) (SW8 (nat_lit 55)) = true := by
  quickRfl

theorem c36_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [10, 3]
    (SW8 (nat_lit 53))) (SW8 (nat_lit 54)) = true := by
  quickRfl

theorem c36_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 5]
    (SW8 (nat_lit 52))) (SW8 (nat_lit 53)) = true := by
  quickRfl

theorem c36_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 6]
    (SW8 (nat_lit 51))) (SW8 (nat_lit 52)) = true := by
  quickRfl

theorem c36_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 5]
    (SW8 (nat_lit 50))) (SW8 (nat_lit 51)) = true := by
  quickRfl

theorem c36_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 9]
    (SW8 (nat_lit 49))) (SW8 (nat_lit 50)) = true := by
  quickRfl

theorem c36_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [24, 25]
    (SW8 (nat_lit 48))) (SW8 (nat_lit 49)) = true := by
  quickRfl

theorem c36_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [25, 5]
    (SW8 (nat_lit 47))) (SW8 (nat_lit 48)) = true := by
  quickRfl

theorem c36_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 9]
    (SW8 (nat_lit 46))) (SW8 (nat_lit 47)) = true := by
  quickRfl

theorem c36_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 24]
    (SW8 (nat_lit 45))) (SW8 (nat_lit 46)) = true := by
  quickRfl

theorem c36_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 4]
    (SW8 (nat_lit 44))) (SW8 (nat_lit 45)) = true := by
  quickRfl

theorem c36_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [24, 5]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 36))) (SW8 (nat_lit 44)) = true := by
  quickRfl

theorem c36_w : WC (nat_lit 36) = [17, 21] ++ ([21, 21] ++ ([22, 24] ++ ([4, 10] ++ ([12, 3] ++ ([5, 24] ++ ([19, 8] ++ ([3, 19] ++ ([20, 18] ++ ([10, 3] ++ ([20, 5] ++ ([6, 6] ++ ([9, 5] ++ ([3, 9] ++ ([24, 25] ++ ([25, 5] ++ ([6, 9] ++ ([17, 24] ++ ([4, 4] ++ ([24, 5]))))))))))))))))))) := rfl

theorem c36 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 36))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 36))) (ST (nat_lit 36)) = true :=
  beq_wordMul_of_eq c36_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c36_p19 c36_p18) c36_p17) c36_p16) c36_p15) c36_p14) c36_p13) c36_p12) c36_p11) c36_p10) c36_p9) c36_p8) c36_p7) c36_p6) c36_p5) c36_p4) c36_p3) c36_p2) c36_p1) c36_p0)

end CFSG.KD.Fi24Ext

end
