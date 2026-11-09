module

public import Certificates.Kernel.Sporadic.Fi24Ext.Chunks
public import Certificates.Kernel.Sporadic.Fi24Fix.Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree CFSG.KD.Fi24Ext SW3 "Certificates/Kernel/Sporadic/Fi24Ext/data/w3.bin" 152491 4 9454442 6317950585394614105

public section

set_option Elab.async false

open CFSG.KC.Fi24Fix (beq_wordMul_append beq_wordMul_of_eq)

namespace CFSG.KD.Fi24Ext

theorem c14_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 19]
    (SW3 (nat_lit 18))) (ST (nat_lit 14)) = true := by
  quickRfl

theorem c14_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 7]
    (SW3 (nat_lit 17))) (SW3 (nat_lit 18)) = true := by
  quickRfl

theorem c14_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 18]
    (SW3 (nat_lit 16))) (SW3 (nat_lit 17)) = true := by
  quickRfl

theorem c14_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 6]
    (SW3 (nat_lit 15))) (SW3 (nat_lit 16)) = true := by
  quickRfl

theorem c14_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 17]
    (SW3 (nat_lit 14))) (SW3 (nat_lit 15)) = true := by
  quickRfl

theorem c14_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 3]
    (SW3 (nat_lit 13))) (SW3 (nat_lit 14)) = true := by
  quickRfl

theorem c14_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 5]
    (SW3 (nat_lit 12))) (SW3 (nat_lit 13)) = true := by
  quickRfl

theorem c14_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 4]
    (SW3 (nat_lit 11))) (SW3 (nat_lit 12)) = true := by
  quickRfl

theorem c14_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 6]
    (SW3 (nat_lit 10))) (SW3 (nat_lit 11)) = true := by
  quickRfl

theorem c14_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 7]
    (SW3 (nat_lit 9))) (SW3 (nat_lit 10)) = true := by
  quickRfl

theorem c14_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 18]
    (SW3 (nat_lit 8))) (SW3 (nat_lit 9)) = true := by
  quickRfl

theorem c14_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 20]
    (SW3 (nat_lit 7))) (SW3 (nat_lit 8)) = true := by
  quickRfl

theorem c14_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 18]
    (SW3 (nat_lit 6))) (SW3 (nat_lit 7)) = true := by
  quickRfl

theorem c14_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 19]
    (SW3 (nat_lit 5))) (SW3 (nat_lit 6)) = true := by
  quickRfl

theorem c14_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 4]
    (SW3 (nat_lit 4))) (SW3 (nat_lit 5)) = true := by
  quickRfl

theorem c14_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 3]
    (SW3 (nat_lit 3))) (SW3 (nat_lit 4)) = true := by
  quickRfl

theorem c14_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 3]
    (SW3 (nat_lit 2))) (SW3 (nat_lit 3)) = true := by
  quickRfl

theorem c14_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 7]
    (SW3 (nat_lit 1))) (SW3 (nat_lit 2)) = true := by
  quickRfl

theorem c14_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 3]
    (SW3 (nat_lit 0))) (SW3 (nat_lit 1)) = true := by
  quickRfl

theorem c14_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 3]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 14))) (SW3 (nat_lit 0)) = true := by
  quickRfl

theorem c14_w : WC (nat_lit 14) = [18, 19] ++ ([3, 7] ++ ([19, 18] ++ ([18, 6] ++ ([5, 17] ++ ([6, 3] ++ ([4, 5] ++ ([19, 4] ++ ([3, 6] ++ ([5, 7] ++ ([3, 18] ++ ([18, 20] ++ ([6, 18] ++ ([7, 19] ++ ([3, 4] ++ ([18, 3] ++ ([20, 3] ++ ([7, 7] ++ ([7, 3] ++ ([6, 3]))))))))))))))))))) := rfl

theorem c14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 14))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 14))) (ST (nat_lit 14)) = true :=
  beq_wordMul_of_eq c14_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c14_p19 c14_p18) c14_p17) c14_p16) c14_p15) c14_p14) c14_p13) c14_p12) c14_p11) c14_p10) c14_p9) c14_p8) c14_p7) c14_p6) c14_p5) c14_p4) c14_p3) c14_p2) c14_p1) c14_p0)

theorem c15_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 20]
    (SW3 (nat_lit 23))) (ST (nat_lit 15)) = true := by
  quickRfl

theorem c15_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 20]
    (SW3 (nat_lit 22))) (SW3 (nat_lit 23)) = true := by
  quickRfl

theorem c15_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 19]
    (SW3 (nat_lit 21))) (SW3 (nat_lit 22)) = true := by
  quickRfl

theorem c15_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 18]
    (SW3 (nat_lit 20))) (SW3 (nat_lit 21)) = true := by
  quickRfl

theorem c15_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 3]
    (SW3 (nat_lit 19))) (SW3 (nat_lit 20)) = true := by
  quickRfl

theorem c15_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 4]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 15))) (SW3 (nat_lit 19)) = true := by
  quickRfl

theorem c15_w : WC (nat_lit 15) = [18, 20] ++ ([20, 20] ++ ([5, 19] ++ ([19, 18] ++ ([6, 3] ++ ([19, 4]))))) := rfl

theorem c15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 15))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 15))) (ST (nat_lit 15)) = true :=
  beq_wordMul_of_eq c15_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c15_p5 c15_p4) c15_p3) c15_p2) c15_p1) c15_p0)

theorem c16_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 7]
    (SW3 (nat_lit 42))) (ST (nat_lit 16)) = true := by
  quickRfl

theorem c16_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 17]
    (SW3 (nat_lit 41))) (SW3 (nat_lit 42)) = true := by
  quickRfl

theorem c16_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 19]
    (SW3 (nat_lit 40))) (SW3 (nat_lit 41)) = true := by
  quickRfl

theorem c16_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 5]
    (SW3 (nat_lit 39))) (SW3 (nat_lit 40)) = true := by
  quickRfl

theorem c16_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 8]
    (SW3 (nat_lit 38))) (SW3 (nat_lit 39)) = true := by
  quickRfl

theorem c16_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 21]
    (SW3 (nat_lit 37))) (SW3 (nat_lit 38)) = true := by
  quickRfl

theorem c16_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 20]
    (SW3 (nat_lit 36))) (SW3 (nat_lit 37)) = true := by
  quickRfl

theorem c16_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 4]
    (SW3 (nat_lit 35))) (SW3 (nat_lit 36)) = true := by
  quickRfl

theorem c16_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 6]
    (SW3 (nat_lit 34))) (SW3 (nat_lit 35)) = true := by
  quickRfl

theorem c16_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 7]
    (SW3 (nat_lit 33))) (SW3 (nat_lit 34)) = true := by
  quickRfl

theorem c16_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 5]
    (SW3 (nat_lit 32))) (SW3 (nat_lit 33)) = true := by
  quickRfl

theorem c16_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 19]
    (SW3 (nat_lit 31))) (SW3 (nat_lit 32)) = true := by
  quickRfl

theorem c16_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 20]
    (SW3 (nat_lit 30))) (SW3 (nat_lit 31)) = true := by
  quickRfl

theorem c16_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 7]
    (SW3 (nat_lit 29))) (SW3 (nat_lit 30)) = true := by
  quickRfl

theorem c16_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 17]
    (SW3 (nat_lit 28))) (SW3 (nat_lit 29)) = true := by
  quickRfl

theorem c16_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 4]
    (SW3 (nat_lit 27))) (SW3 (nat_lit 28)) = true := by
  quickRfl

theorem c16_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 7]
    (SW3 (nat_lit 26))) (SW3 (nat_lit 27)) = true := by
  quickRfl

theorem c16_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 4]
    (SW3 (nat_lit 25))) (SW3 (nat_lit 26)) = true := by
  quickRfl

theorem c16_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 7]
    (SW3 (nat_lit 24))) (SW3 (nat_lit 25)) = true := by
  quickRfl

theorem c16_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 3]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 16))) (SW3 (nat_lit 24)) = true := by
  quickRfl

theorem c16_w : WC (nat_lit 16) = [18, 7] ++ ([19, 17] ++ ([21, 19] ++ ([3, 5] ++ ([4, 8] ++ ([20, 21] ++ ([20, 20] ++ ([21, 4] ++ ([8, 6] ++ ([3, 7] ++ ([3, 5] ++ ([21, 19] ++ ([4, 20] ++ ([18, 7] ++ ([18, 17] ++ ([21, 4] ++ ([5, 7] ++ ([7, 4] ++ ([4, 7] ++ ([8, 3]))))))))))))))))))) := rfl

theorem c16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 16))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 16))) (ST (nat_lit 16)) = true :=
  beq_wordMul_of_eq c16_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c16_p19 c16_p18) c16_p17) c16_p16) c16_p15) c16_p14) c16_p13) c16_p12) c16_p11) c16_p10) c16_p9) c16_p8) c16_p7) c16_p6) c16_p5) c16_p4) c16_p3) c16_p2) c16_p1) c16_p0)

theorem c17_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 6]
    (SW3 (nat_lit 61))) (ST (nat_lit 17)) = true := by
  quickRfl

theorem c17_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 8]
    (SW3 (nat_lit 60))) (SW3 (nat_lit 61)) = true := by
  quickRfl

theorem c17_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 5]
    (SW3 (nat_lit 59))) (SW3 (nat_lit 60)) = true := by
  quickRfl

theorem c17_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 18]
    (SW3 (nat_lit 58))) (SW3 (nat_lit 59)) = true := by
  quickRfl

theorem c17_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 5]
    (SW3 (nat_lit 57))) (SW3 (nat_lit 58)) = true := by
  quickRfl

theorem c17_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 5]
    (SW3 (nat_lit 56))) (SW3 (nat_lit 57)) = true := by
  quickRfl

theorem c17_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 4]
    (SW3 (nat_lit 55))) (SW3 (nat_lit 56)) = true := by
  quickRfl

theorem c17_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 19]
    (SW3 (nat_lit 54))) (SW3 (nat_lit 55)) = true := by
  quickRfl

theorem c17_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 3]
    (SW3 (nat_lit 53))) (SW3 (nat_lit 54)) = true := by
  quickRfl

theorem c17_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 3]
    (SW3 (nat_lit 52))) (SW3 (nat_lit 53)) = true := by
  quickRfl

theorem c17_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 6]
    (SW3 (nat_lit 51))) (SW3 (nat_lit 52)) = true := by
  quickRfl

theorem c17_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 20]
    (SW3 (nat_lit 50))) (SW3 (nat_lit 51)) = true := by
  quickRfl

theorem c17_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 20]
    (SW3 (nat_lit 49))) (SW3 (nat_lit 50)) = true := by
  quickRfl

theorem c17_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 8]
    (SW3 (nat_lit 48))) (SW3 (nat_lit 49)) = true := by
  quickRfl

theorem c17_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 6]
    (SW3 (nat_lit 47))) (SW3 (nat_lit 48)) = true := by
  quickRfl

theorem c17_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 20]
    (SW3 (nat_lit 46))) (SW3 (nat_lit 47)) = true := by
  quickRfl

theorem c17_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 20]
    (SW3 (nat_lit 45))) (SW3 (nat_lit 46)) = true := by
  quickRfl

theorem c17_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 8]
    (SW3 (nat_lit 44))) (SW3 (nat_lit 45)) = true := by
  quickRfl

theorem c17_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 8]
    (SW3 (nat_lit 43))) (SW3 (nat_lit 44)) = true := by
  quickRfl

theorem c17_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 21]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 17))) (SW3 (nat_lit 43)) = true := by
  quickRfl

theorem c17_w : WC (nat_lit 17) = [8, 6] ++ ([6, 8] ++ ([4, 5] ++ ([20, 18] ++ ([3, 5] ++ ([5, 5] ++ ([6, 4] ++ ([20, 19] ++ ([21, 3] ++ ([20, 3] ++ ([7, 6] ++ ([8, 20] ++ ([6, 20] ++ ([19, 8] ++ ([6, 6] ++ ([8, 20] ++ ([17, 20] ++ ([17, 8] ++ ([8, 8] ++ ([6, 21]))))))))))))))))))) := rfl

theorem c17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 17))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 17))) (ST (nat_lit 17)) = true :=
  beq_wordMul_of_eq c17_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c17_p19 c17_p18) c17_p17) c17_p16) c17_p15) c17_p14) c17_p13) c17_p12) c17_p11) c17_p10) c17_p9) c17_p8) c17_p7) c17_p6) c17_p5) c17_p4) c17_p3) c17_p2) c17_p1) c17_p0)

end CFSG.KD.Fi24Ext

end
