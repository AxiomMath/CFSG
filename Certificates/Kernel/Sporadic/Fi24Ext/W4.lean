module

public import Certificates.Kernel.Sporadic.Fi24Ext.Chunks
public import Certificates.Kernel.Sporadic.Fi24Fix.Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree CFSG.KD.Fi24Ext SW4 "Certificates/Kernel/Sporadic/Fi24Ext/data/w4.bin" 152491 4 8844478 17106685365296020341

public section

set_option Elab.async false

open CFSG.KC.Fi24Fix (beq_wordMul_append beq_wordMul_of_eq)

namespace CFSG.KD.Fi24Ext

theorem c10_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 5]
    (SW4 (nat_lit 18))) (ST (nat_lit 10)) = true := by
  quickRfl

theorem c10_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 6]
    (SW4 (nat_lit 17))) (SW4 (nat_lit 18)) = true := by
  quickRfl

theorem c10_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 19]
    (SW4 (nat_lit 16))) (SW4 (nat_lit 17)) = true := by
  quickRfl

theorem c10_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 5]
    (SW4 (nat_lit 15))) (SW4 (nat_lit 16)) = true := by
  quickRfl

theorem c10_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 18]
    (SW4 (nat_lit 14))) (SW4 (nat_lit 15)) = true := by
  quickRfl

theorem c10_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 18]
    (SW4 (nat_lit 13))) (SW4 (nat_lit 14)) = true := by
  quickRfl

theorem c10_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 17]
    (SW4 (nat_lit 12))) (SW4 (nat_lit 13)) = true := by
  quickRfl

theorem c10_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 4]
    (SW4 (nat_lit 11))) (SW4 (nat_lit 12)) = true := by
  quickRfl

theorem c10_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 5]
    (SW4 (nat_lit 10))) (SW4 (nat_lit 11)) = true := by
  quickRfl

theorem c10_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 6]
    (SW4 (nat_lit 9))) (SW4 (nat_lit 10)) = true := by
  quickRfl

theorem c10_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 5]
    (SW4 (nat_lit 8))) (SW4 (nat_lit 9)) = true := by
  quickRfl

theorem c10_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 5]
    (SW4 (nat_lit 7))) (SW4 (nat_lit 8)) = true := by
  quickRfl

theorem c10_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 4]
    (SW4 (nat_lit 6))) (SW4 (nat_lit 7)) = true := by
  quickRfl

theorem c10_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 3]
    (SW4 (nat_lit 5))) (SW4 (nat_lit 6)) = true := by
  quickRfl

theorem c10_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 4]
    (SW4 (nat_lit 4))) (SW4 (nat_lit 5)) = true := by
  quickRfl

theorem c10_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 18]
    (SW4 (nat_lit 3))) (SW4 (nat_lit 4)) = true := by
  quickRfl

theorem c10_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 6]
    (SW4 (nat_lit 2))) (SW4 (nat_lit 3)) = true := by
  quickRfl

theorem c10_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 5]
    (SW4 (nat_lit 1))) (SW4 (nat_lit 2)) = true := by
  quickRfl

theorem c10_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 17]
    (SW4 (nat_lit 0))) (SW4 (nat_lit 1)) = true := by
  quickRfl

theorem c10_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 5]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 10))) (SW4 (nat_lit 0)) = true := by
  quickRfl

theorem c10_w : WC (nat_lit 10) = [6, 5] ++ ([6, 6] ++ ([18, 19] ++ ([19, 5] ++ ([19, 18] ++ ([17, 18] ++ ([3, 17] ++ ([5, 4] ++ ([19, 5] ++ ([6, 6] ++ ([5, 5] ++ ([5, 5] ++ ([19, 4] ++ ([19, 3] ++ ([19, 4] ++ ([19, 18] ++ ([3, 6] ++ ([6, 5] ++ ([3, 17] ++ ([3, 5]))))))))))))))))))) := rfl

theorem c10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 10))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 10))) (ST (nat_lit 10)) = true :=
  beq_wordMul_of_eq c10_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c10_p19 c10_p18) c10_p17) c10_p16) c10_p15) c10_p14) c10_p13) c10_p12) c10_p11) c10_p10) c10_p9) c10_p8) c10_p7) c10_p6) c10_p5) c10_p4) c10_p3) c10_p2) c10_p1) c10_p0)

theorem c11_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5]
    (SW4 (nat_lit 19))) (ST (nat_lit 11)) = true := by
  quickRfl

theorem c11_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 18]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 11))) (SW4 (nat_lit 19)) = true := by
  quickRfl

theorem c11_w : WC (nat_lit 11) = [5] ++ ([6, 18]) := rfl

theorem c11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 11))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 11))) (ST (nat_lit 11)) = true :=
  beq_wordMul_of_eq c11_w (beq_wordMul_append c11_p1 c11_p0)

theorem c12_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 3]
    (SW4 (nat_lit 38))) (ST (nat_lit 12)) = true := by
  quickRfl

theorem c12_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 7]
    (SW4 (nat_lit 37))) (SW4 (nat_lit 38)) = true := by
  quickRfl

theorem c12_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 7]
    (SW4 (nat_lit 36))) (SW4 (nat_lit 37)) = true := by
  quickRfl

theorem c12_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 20]
    (SW4 (nat_lit 35))) (SW4 (nat_lit 36)) = true := by
  quickRfl

theorem c12_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 7]
    (SW4 (nat_lit 34))) (SW4 (nat_lit 35)) = true := by
  quickRfl

theorem c12_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 7]
    (SW4 (nat_lit 33))) (SW4 (nat_lit 34)) = true := by
  quickRfl

theorem c12_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 3]
    (SW4 (nat_lit 32))) (SW4 (nat_lit 33)) = true := by
  quickRfl

theorem c12_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 3]
    (SW4 (nat_lit 31))) (SW4 (nat_lit 32)) = true := by
  quickRfl

theorem c12_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 3]
    (SW4 (nat_lit 30))) (SW4 (nat_lit 31)) = true := by
  quickRfl

theorem c12_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 18]
    (SW4 (nat_lit 29))) (SW4 (nat_lit 30)) = true := by
  quickRfl

theorem c12_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 6]
    (SW4 (nat_lit 28))) (SW4 (nat_lit 29)) = true := by
  quickRfl

theorem c12_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 17]
    (SW4 (nat_lit 27))) (SW4 (nat_lit 28)) = true := by
  quickRfl

theorem c12_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 3]
    (SW4 (nat_lit 26))) (SW4 (nat_lit 27)) = true := by
  quickRfl

theorem c12_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 18]
    (SW4 (nat_lit 25))) (SW4 (nat_lit 26)) = true := by
  quickRfl

theorem c12_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 20]
    (SW4 (nat_lit 24))) (SW4 (nat_lit 25)) = true := by
  quickRfl

theorem c12_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 17]
    (SW4 (nat_lit 23))) (SW4 (nat_lit 24)) = true := by
  quickRfl

theorem c12_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 3]
    (SW4 (nat_lit 22))) (SW4 (nat_lit 23)) = true := by
  quickRfl

theorem c12_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 18]
    (SW4 (nat_lit 21))) (SW4 (nat_lit 22)) = true := by
  quickRfl

theorem c12_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 18]
    (SW4 (nat_lit 20))) (SW4 (nat_lit 21)) = true := by
  quickRfl

theorem c12_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 17]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 12))) (SW4 (nat_lit 20)) = true := by
  quickRfl

theorem c12_w : WC (nat_lit 12) = [6, 3] ++ ([4, 7] ++ ([5, 7] ++ ([5, 20] ++ ([19, 7] ++ ([17, 7] ++ ([5, 3] ++ ([7, 3] ++ ([5, 3] ++ ([18, 18] ++ ([7, 6] ++ ([20, 17] ++ ([19, 3] ++ ([18, 18] ++ ([3, 20] ++ ([17, 17] ++ ([7, 3] ++ ([17, 18] ++ ([18, 18] ++ ([20, 17]))))))))))))))))))) := rfl

theorem c12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 12))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 12))) (ST (nat_lit 12)) = true :=
  beq_wordMul_of_eq c12_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c12_p19 c12_p18) c12_p17) c12_p16) c12_p15) c12_p14) c12_p13) c12_p12) c12_p11) c12_p10) c12_p9) c12_p8) c12_p7) c12_p6) c12_p5) c12_p4) c12_p3) c12_p2) c12_p1) c12_p0)

theorem c13_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 18]
    (SW4 (nat_lit 57))) (ST (nat_lit 13)) = true := by
  quickRfl

theorem c13_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 4]
    (SW4 (nat_lit 56))) (SW4 (nat_lit 57)) = true := by
  quickRfl

theorem c13_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 3]
    (SW4 (nat_lit 55))) (SW4 (nat_lit 56)) = true := by
  quickRfl

theorem c13_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 4]
    (SW4 (nat_lit 54))) (SW4 (nat_lit 55)) = true := by
  quickRfl

theorem c13_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 18]
    (SW4 (nat_lit 53))) (SW4 (nat_lit 54)) = true := by
  quickRfl

theorem c13_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 18]
    (SW4 (nat_lit 52))) (SW4 (nat_lit 53)) = true := by
  quickRfl

theorem c13_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [7, 3]
    (SW4 (nat_lit 51))) (SW4 (nat_lit 52)) = true := by
  quickRfl

theorem c13_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 19]
    (SW4 (nat_lit 50))) (SW4 (nat_lit 51)) = true := by
  quickRfl

theorem c13_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 20]
    (SW4 (nat_lit 49))) (SW4 (nat_lit 50)) = true := by
  quickRfl

theorem c13_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 3]
    (SW4 (nat_lit 48))) (SW4 (nat_lit 49)) = true := by
  quickRfl

theorem c13_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 18]
    (SW4 (nat_lit 47))) (SW4 (nat_lit 48)) = true := by
  quickRfl

theorem c13_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 3]
    (SW4 (nat_lit 46))) (SW4 (nat_lit 47)) = true := by
  quickRfl

theorem c13_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [6, 6]
    (SW4 (nat_lit 45))) (SW4 (nat_lit 46)) = true := by
  quickRfl

theorem c13_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 3]
    (SW4 (nat_lit 44))) (SW4 (nat_lit 45)) = true := by
  quickRfl

theorem c13_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 3]
    (SW4 (nat_lit 43))) (SW4 (nat_lit 44)) = true := by
  quickRfl

theorem c13_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 5]
    (SW4 (nat_lit 42))) (SW4 (nat_lit 43)) = true := by
  quickRfl

theorem c13_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 5]
    (SW4 (nat_lit 41))) (SW4 (nat_lit 42)) = true := by
  quickRfl

theorem c13_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 17]
    (SW4 (nat_lit 40))) (SW4 (nat_lit 41)) = true := by
  quickRfl

theorem c13_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 7]
    (SW4 (nat_lit 39))) (SW4 (nat_lit 40)) = true := by
  quickRfl

theorem c13_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 18]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 13))) (SW4 (nat_lit 39)) = true := by
  quickRfl

theorem c13_w : WC (nat_lit 13) = [20, 18] ++ ([4, 4] ++ ([18, 3] ++ ([5, 4] ++ ([3, 18] ++ ([3, 18] ++ ([7, 3] ++ ([20, 19] ++ ([3, 20] ++ ([4, 3] ++ ([18, 18] ++ ([18, 3] ++ ([6, 6] ++ ([20, 3] ++ ([17, 3] ++ ([20, 5] ++ ([4, 5] ++ ([19, 17] ++ ([3, 7] ++ ([3, 18]))))))))))))))))))) := rfl

theorem c13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 13))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 13))) (ST (nat_lit 13)) = true :=
  beq_wordMul_of_eq c13_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c13_p19 c13_p18) c13_p17) c13_p16) c13_p15) c13_p14) c13_p13) c13_p12) c13_p11) c13_p10) c13_p9) c13_p8) c13_p7) c13_p6) c13_p5) c13_p4) c13_p3) c13_p2) c13_p1) c13_p0)

end CFSG.KD.Fi24Ext

end
