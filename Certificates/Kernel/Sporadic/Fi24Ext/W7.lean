module

public import Certificates.Kernel.Sporadic.Fi24Ext.Chunks
public import Certificates.Kernel.Sporadic.Fi24Fix.Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree CFSG.KD.Fi24Ext SW7 "Certificates/Kernel/Sporadic/Fi24Ext/data/w7.bin" 152491 4 8691987 10062072582908737478

public section

set_option Elab.async false

open CFSG.KC.Fi24Fix (beq_wordMul_append beq_wordMul_of_eq)

namespace CFSG.KD.Fi24Ext

theorem c30_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 10]
    (SW7 (nat_lit 18))) (ST (nat_lit 30)) = true := by
  quickRfl

theorem c30_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 7]
    (SW7 (nat_lit 17))) (SW7 (nat_lit 18)) = true := by
  quickRfl

theorem c30_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 9]
    (SW7 (nat_lit 16))) (SW7 (nat_lit 17)) = true := by
  quickRfl

theorem c30_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 4]
    (SW7 (nat_lit 15))) (SW7 (nat_lit 16)) = true := by
  quickRfl

theorem c30_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 21]
    (SW7 (nat_lit 14))) (SW7 (nat_lit 15)) = true := by
  quickRfl

theorem c30_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 4]
    (SW7 (nat_lit 13))) (SW7 (nat_lit 14)) = true := by
  quickRfl

theorem c30_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [24, 3]
    (SW7 (nat_lit 12))) (SW7 (nat_lit 13)) = true := by
  quickRfl

theorem c30_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 6]
    (SW7 (nat_lit 11))) (SW7 (nat_lit 12)) = true := by
  quickRfl

theorem c30_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 4]
    (SW7 (nat_lit 10))) (SW7 (nat_lit 11)) = true := by
  quickRfl

theorem c30_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 3]
    (SW7 (nat_lit 9))) (SW7 (nat_lit 10)) = true := by
  quickRfl

theorem c30_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 5]
    (SW7 (nat_lit 8))) (SW7 (nat_lit 9)) = true := by
  quickRfl

theorem c30_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [24, 8]
    (SW7 (nat_lit 7))) (SW7 (nat_lit 8)) = true := by
  quickRfl

theorem c30_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 24]
    (SW7 (nat_lit 6))) (SW7 (nat_lit 7)) = true := by
  quickRfl

theorem c30_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 5]
    (SW7 (nat_lit 5))) (SW7 (nat_lit 6)) = true := by
  quickRfl

theorem c30_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 7]
    (SW7 (nat_lit 4))) (SW7 (nat_lit 5)) = true := by
  quickRfl

theorem c30_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 6]
    (SW7 (nat_lit 3))) (SW7 (nat_lit 4)) = true := by
  quickRfl

theorem c30_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 8]
    (SW7 (nat_lit 2))) (SW7 (nat_lit 3)) = true := by
  quickRfl

theorem c30_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 21]
    (SW7 (nat_lit 1))) (SW7 (nat_lit 2)) = true := by
  quickRfl

theorem c30_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 3]
    (SW7 (nat_lit 0))) (SW7 (nat_lit 1)) = true := by
  quickRfl

theorem c30_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 4]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 30))) (SW7 (nat_lit 0)) = true := by
  quickRfl

theorem c30_w : WC (nat_lit 30) = [7, 10] ++ ([3, 7] ++ ([6, 9] ++ ([8, 4] ++ ([9, 21] ++ ([23, 4] ++ ([24, 3] ++ ([17, 6] ++ ([21, 4] ++ ([23, 3] ++ ([19, 5] ++ ([24, 8] ++ ([19, 24] ++ ([22, 5] ++ ([9, 7] ++ ([22, 6] ++ ([18, 8] ++ ([6, 21] ++ ([23, 3] ++ ([5, 4]))))))))))))))))))) := rfl

theorem c30 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 30))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 30))) (ST (nat_lit 30)) = true :=
  beq_wordMul_of_eq c30_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c30_p19 c30_p18) c30_p17) c30_p16) c30_p15) c30_p14) c30_p13) c30_p12) c30_p11) c30_p10) c30_p9) c30_p8) c30_p7) c30_p6) c30_p5) c30_p4) c30_p3) c30_p2) c30_p1) c30_p0)

theorem c31_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 17]
    (SW7 (nat_lit 37))) (ST (nat_lit 31)) = true := by
  quickRfl

theorem c31_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 17]
    (SW7 (nat_lit 36))) (SW7 (nat_lit 37)) = true := by
  quickRfl

theorem c31_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [11, 7]
    (SW7 (nat_lit 35))) (SW7 (nat_lit 36)) = true := by
  quickRfl

theorem c31_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 3]
    (SW7 (nat_lit 34))) (SW7 (nat_lit 35)) = true := by
  quickRfl

theorem c31_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 6]
    (SW7 (nat_lit 33))) (SW7 (nat_lit 34)) = true := by
  quickRfl

theorem c31_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 11]
    (SW7 (nat_lit 32))) (SW7 (nat_lit 33)) = true := by
  quickRfl

theorem c31_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 23]
    (SW7 (nat_lit 31))) (SW7 (nat_lit 32)) = true := by
  quickRfl

theorem c31_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 10]
    (SW7 (nat_lit 30))) (SW7 (nat_lit 31)) = true := by
  quickRfl

theorem c31_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 22]
    (SW7 (nat_lit 29))) (SW7 (nat_lit 30)) = true := by
  quickRfl

theorem c31_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 4]
    (SW7 (nat_lit 28))) (SW7 (nat_lit 29)) = true := by
  quickRfl

theorem c31_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 9]
    (SW7 (nat_lit 27))) (SW7 (nat_lit 28)) = true := by
  quickRfl

theorem c31_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 9]
    (SW7 (nat_lit 26))) (SW7 (nat_lit 27)) = true := by
  quickRfl

theorem c31_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [11, 8]
    (SW7 (nat_lit 25))) (SW7 (nat_lit 26)) = true := by
  quickRfl

theorem c31_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 18]
    (SW7 (nat_lit 24))) (SW7 (nat_lit 25)) = true := by
  quickRfl

theorem c31_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [11, 9]
    (SW7 (nat_lit 23))) (SW7 (nat_lit 24)) = true := by
  quickRfl

theorem c31_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 21]
    (SW7 (nat_lit 22))) (SW7 (nat_lit 23)) = true := by
  quickRfl

theorem c31_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 3]
    (SW7 (nat_lit 21))) (SW7 (nat_lit 22)) = true := by
  quickRfl

theorem c31_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 7]
    (SW7 (nat_lit 20))) (SW7 (nat_lit 21)) = true := by
  quickRfl

theorem c31_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 21]
    (SW7 (nat_lit 19))) (SW7 (nat_lit 20)) = true := by
  quickRfl

theorem c31_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 7]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 31))) (SW7 (nat_lit 19)) = true := by
  quickRfl

theorem c31_w : WC (nat_lit 31) = [17, 17] ++ ([21, 17] ++ ([11, 7] ++ ([6, 3] ++ ([22, 6] ++ ([17, 11] ++ ([3, 23] ++ ([17, 10] ++ ([5, 22] ++ ([5, 4] ++ ([9, 9] ++ ([4, 9] ++ ([11, 8] ++ ([17, 18] ++ ([11, 9] ++ ([17, 21] ++ ([6, 3] ++ ([22, 7] ++ ([5, 21] ++ ([7, 7]))))))))))))))))))) := rfl

theorem c31 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 31))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 31))) (ST (nat_lit 31)) = true :=
  beq_wordMul_of_eq c31_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c31_p19 c31_p18) c31_p17) c31_p16) c31_p15) c31_p14) c31_p13) c31_p12) c31_p11) c31_p10) c31_p9) c31_p8) c31_p7) c31_p6) c31_p5) c31_p4) c31_p3) c31_p2) c31_p1) c31_p0)

theorem c32_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 11]
    (SW7 (nat_lit 56))) (ST (nat_lit 32)) = true := by
  quickRfl

theorem c32_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 9]
    (SW7 (nat_lit 55))) (SW7 (nat_lit 56)) = true := by
  quickRfl

theorem c32_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 18]
    (SW7 (nat_lit 54))) (SW7 (nat_lit 55)) = true := by
  quickRfl

theorem c32_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 23]
    (SW7 (nat_lit 53))) (SW7 (nat_lit 54)) = true := by
  quickRfl

theorem c32_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 22]
    (SW7 (nat_lit 52))) (SW7 (nat_lit 53)) = true := by
  quickRfl

theorem c32_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 10]
    (SW7 (nat_lit 51))) (SW7 (nat_lit 52)) = true := by
  quickRfl

theorem c32_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 21]
    (SW7 (nat_lit 50))) (SW7 (nat_lit 51)) = true := by
  quickRfl

theorem c32_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 21]
    (SW7 (nat_lit 49))) (SW7 (nat_lit 50)) = true := by
  quickRfl

theorem c32_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 20]
    (SW7 (nat_lit 48))) (SW7 (nat_lit 49)) = true := by
  quickRfl

theorem c32_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [22, 11]
    (SW7 (nat_lit 47))) (SW7 (nat_lit 48)) = true := by
  quickRfl

theorem c32_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 22]
    (SW7 (nat_lit 46))) (SW7 (nat_lit 47)) = true := by
  quickRfl

theorem c32_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 21]
    (SW7 (nat_lit 45))) (SW7 (nat_lit 46)) = true := by
  quickRfl

theorem c32_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 7]
    (SW7 (nat_lit 44))) (SW7 (nat_lit 45)) = true := by
  quickRfl

theorem c32_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [9, 19]
    (SW7 (nat_lit 43))) (SW7 (nat_lit 44)) = true := by
  quickRfl

theorem c32_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [11, 23]
    (SW7 (nat_lit 42))) (SW7 (nat_lit 43)) = true := by
  quickRfl

theorem c32_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 20]
    (SW7 (nat_lit 41))) (SW7 (nat_lit 42)) = true := by
  quickRfl

theorem c32_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [10, 17]
    (SW7 (nat_lit 40))) (SW7 (nat_lit 41)) = true := by
  quickRfl

theorem c32_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 5]
    (SW7 (nat_lit 39))) (SW7 (nat_lit 40)) = true := by
  quickRfl

theorem c32_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 7]
    (SW7 (nat_lit 38))) (SW7 (nat_lit 39)) = true := by
  quickRfl

theorem c32_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 20]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 32))) (SW7 (nat_lit 38)) = true := by
  quickRfl

theorem c32_w : WC (nat_lit 32) = [8, 11] ++ ([18, 9] ++ ([17, 18] ++ ([20, 23] ++ ([19, 22] ++ ([18, 10] ++ ([21, 21] ++ ([19, 21] ++ ([20, 20] ++ ([22, 11] ++ ([3, 22] ++ ([3, 21] ++ ([4, 7] ++ ([9, 19] ++ ([11, 23] ++ ([23, 20] ++ ([10, 17] ++ ([7, 5] ++ ([5, 7] ++ ([4, 20]))))))))))))))))))) := rfl

theorem c32 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 32))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 32))) (ST (nat_lit 32)) = true :=
  beq_wordMul_of_eq c32_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c32_p19 c32_p18) c32_p17) c32_p16) c32_p15) c32_p14) c32_p13) c32_p12) c32_p11) c32_p10) c32_p9) c32_p8) c32_p7) c32_p6) c32_p5) c32_p4) c32_p3) c32_p2) c32_p1) c32_p0)

end CFSG.KD.Fi24Ext

end
