module

public import Certificates.Kernel.Sporadic.Fi24Ext.Chunks
public import Certificates.Kernel.Sporadic.Fi24Fix.Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree CFSG.KD.Fi24Ext SW0 "Certificates/Kernel/Sporadic/Fi24Ext/data/w0.bin" 152491 4 9301951 14482816863431589468

public section

set_option Elab.async false

open CFSG.KC.Fi24Fix (beq_wordMul_append beq_wordMul_of_eq)

namespace CFSG.KD.Fi24Ext

theorem c0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 0))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 0))) (ST (nat_lit 0)) = true := by
  quickRfl

theorem c1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 1))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 1))) (ST (nat_lit 1)) = true := by
  quickRfl

theorem c2_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 3]
    (SW0 (nat_lit 18))) (ST (nat_lit 2)) = true := by
  quickRfl

theorem c2_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 3]
    (SW0 (nat_lit 17))) (SW0 (nat_lit 18)) = true := by
  quickRfl

theorem c2_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 3]
    (SW0 (nat_lit 16))) (SW0 (nat_lit 17)) = true := by
  quickRfl

theorem c2_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 3]
    (SW0 (nat_lit 15))) (SW0 (nat_lit 16)) = true := by
  quickRfl

theorem c2_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 3]
    (SW0 (nat_lit 14))) (SW0 (nat_lit 15)) = true := by
  quickRfl

theorem c2_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 3]
    (SW0 (nat_lit 13))) (SW0 (nat_lit 14)) = true := by
  quickRfl

theorem c2_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 3]
    (SW0 (nat_lit 12))) (SW0 (nat_lit 13)) = true := by
  quickRfl

theorem c2_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 4]
    (SW0 (nat_lit 11))) (SW0 (nat_lit 12)) = true := by
  quickRfl

theorem c2_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 4]
    (SW0 (nat_lit 10))) (SW0 (nat_lit 11)) = true := by
  quickRfl

theorem c2_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 17]
    (SW0 (nat_lit 9))) (SW0 (nat_lit 10)) = true := by
  quickRfl

theorem c2_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 17]
    (SW0 (nat_lit 8))) (SW0 (nat_lit 9)) = true := by
  quickRfl

theorem c2_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 4]
    (SW0 (nat_lit 7))) (SW0 (nat_lit 8)) = true := by
  quickRfl

theorem c2_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 3]
    (SW0 (nat_lit 6))) (SW0 (nat_lit 7)) = true := by
  quickRfl

theorem c2_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 3]
    (SW0 (nat_lit 5))) (SW0 (nat_lit 6)) = true := by
  quickRfl

theorem c2_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 3]
    (SW0 (nat_lit 4))) (SW0 (nat_lit 5)) = true := by
  quickRfl

theorem c2_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 4]
    (SW0 (nat_lit 3))) (SW0 (nat_lit 4)) = true := by
  quickRfl

theorem c2_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 4]
    (SW0 (nat_lit 2))) (SW0 (nat_lit 3)) = true := by
  quickRfl

theorem c2_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 17]
    (SW0 (nat_lit 1))) (SW0 (nat_lit 2)) = true := by
  quickRfl

theorem c2_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 17]
    (SW0 (nat_lit 0))) (SW0 (nat_lit 1)) = true := by
  quickRfl

theorem c2_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 17]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 2))) (SW0 (nat_lit 0)) = true := by
  quickRfl

theorem c2_w : WC (nat_lit 2) = [17, 3] ++ ([4, 3] ++ ([4, 3] ++ ([4, 3] ++ ([17, 3] ++ ([4, 3] ++ ([4, 3] ++ ([4, 4] ++ ([3, 4] ++ ([3, 17] ++ ([3, 17] ++ ([3, 4] ++ ([4, 3] ++ ([4, 3] ++ ([17, 3] ++ ([4, 4] ++ ([4, 4] ++ ([3, 17] ++ ([3, 17] ++ ([17, 17]))))))))))))))))))) := rfl

theorem c2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 2))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 2))) (ST (nat_lit 2)) = true :=
  beq_wordMul_of_eq c2_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c2_p19 c2_p18) c2_p17) c2_p16) c2_p15) c2_p14) c2_p13) c2_p12) c2_p11) c2_p10) c2_p9) c2_p8) c2_p7) c2_p6) c2_p5) c2_p4) c2_p3) c2_p2) c2_p1) c2_p0)

theorem c3_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 17]
    (SW0 (nat_lit 37))) (ST (nat_lit 3)) = true := by
  quickRfl

theorem c3_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 17]
    (SW0 (nat_lit 36))) (SW0 (nat_lit 37)) = true := by
  quickRfl

theorem c3_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 4]
    (SW0 (nat_lit 35))) (SW0 (nat_lit 36)) = true := by
  quickRfl

theorem c3_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 4]
    (SW0 (nat_lit 34))) (SW0 (nat_lit 35)) = true := by
  quickRfl

theorem c3_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 17]
    (SW0 (nat_lit 33))) (SW0 (nat_lit 34)) = true := by
  quickRfl

theorem c3_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 17]
    (SW0 (nat_lit 32))) (SW0 (nat_lit 33)) = true := by
  quickRfl

theorem c3_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 17]
    (SW0 (nat_lit 31))) (SW0 (nat_lit 32)) = true := by
  quickRfl

theorem c3_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 17]
    (SW0 (nat_lit 30))) (SW0 (nat_lit 31)) = true := by
  quickRfl

theorem c3_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 17]
    (SW0 (nat_lit 29))) (SW0 (nat_lit 30)) = true := by
  quickRfl

theorem c3_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 4]
    (SW0 (nat_lit 28))) (SW0 (nat_lit 29)) = true := by
  quickRfl

theorem c3_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 4]
    (SW0 (nat_lit 27))) (SW0 (nat_lit 28)) = true := by
  quickRfl

theorem c3_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 4]
    (SW0 (nat_lit 26))) (SW0 (nat_lit 27)) = true := by
  quickRfl

theorem c3_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 17]
    (SW0 (nat_lit 25))) (SW0 (nat_lit 26)) = true := by
  quickRfl

theorem c3_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 3]
    (SW0 (nat_lit 24))) (SW0 (nat_lit 25)) = true := by
  quickRfl

theorem c3_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 3]
    (SW0 (nat_lit 23))) (SW0 (nat_lit 24)) = true := by
  quickRfl

theorem c3_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 3]
    (SW0 (nat_lit 22))) (SW0 (nat_lit 23)) = true := by
  quickRfl

theorem c3_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 3]
    (SW0 (nat_lit 21))) (SW0 (nat_lit 22)) = true := by
  quickRfl

theorem c3_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 3]
    (SW0 (nat_lit 20))) (SW0 (nat_lit 21)) = true := by
  quickRfl

theorem c3_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 3]
    (SW0 (nat_lit 19))) (SW0 (nat_lit 20)) = true := by
  quickRfl

theorem c3_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 17]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 3))) (SW0 (nat_lit 19)) = true := by
  quickRfl

theorem c3_w : WC (nat_lit 3) = [3, 17] ++ ([3, 17] ++ ([3, 4] ++ ([3, 4] ++ ([3, 17] ++ ([3, 17] ++ ([3, 17] ++ ([3, 17] ++ ([3, 17] ++ ([3, 4] ++ ([4, 4] ++ ([3, 4] ++ ([3, 17] ++ ([17, 3] ++ ([4, 3] ++ ([4, 3] ++ ([4, 3] ++ ([4, 3] ++ ([4, 3] ++ ([17, 17]))))))))))))))))))) := rfl

theorem c3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 3))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 3))) (ST (nat_lit 3)) = true :=
  beq_wordMul_of_eq c3_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c3_p19 c3_p18) c3_p17) c3_p16) c3_p15) c3_p14) c3_p13) c3_p12) c3_p11) c3_p10) c3_p9) c3_p8) c3_p7) c3_p6) c3_p5) c3_p4) c3_p3) c3_p2) c3_p1) c3_p0)

theorem c4_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4]
    (SW0 (nat_lit 41))) (ST (nat_lit 4)) = true := by
  quickRfl

theorem c4_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 17]
    (SW0 (nat_lit 40))) (SW0 (nat_lit 41)) = true := by
  quickRfl

theorem c4_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 4]
    (SW0 (nat_lit 39))) (SW0 (nat_lit 40)) = true := by
  quickRfl

theorem c4_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 4]
    (SW0 (nat_lit 38))) (SW0 (nat_lit 39)) = true := by
  quickRfl

theorem c4_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 4]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 4))) (SW0 (nat_lit 38)) = true := by
  quickRfl

theorem c4_w : WC (nat_lit 4) = [4] ++ ([3, 17] ++ ([3, 4] ++ ([3, 4] ++ ([3, 4])))) := rfl

theorem c4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 4))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 4))) (ST (nat_lit 4)) = true :=
  beq_wordMul_of_eq c4_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c4_p4 c4_p3) c4_p2) c4_p1) c4_p0)

theorem c5_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 17]
    (SW0 (nat_lit 60))) (ST (nat_lit 5)) = true := by
  quickRfl

theorem c5_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 3]
    (SW0 (nat_lit 59))) (SW0 (nat_lit 60)) = true := by
  quickRfl

theorem c5_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [17, 3]
    (SW0 (nat_lit 58))) (SW0 (nat_lit 59)) = true := by
  quickRfl

theorem c5_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 5]
    (SW0 (nat_lit 57))) (SW0 (nat_lit 58)) = true := by
  quickRfl

theorem c5_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 5]
    (SW0 (nat_lit 56))) (SW0 (nat_lit 57)) = true := by
  quickRfl

theorem c5_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 17]
    (SW0 (nat_lit 55))) (SW0 (nat_lit 56)) = true := by
  quickRfl

theorem c5_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 17]
    (SW0 (nat_lit 54))) (SW0 (nat_lit 55)) = true := by
  quickRfl

theorem c5_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 17]
    (SW0 (nat_lit 53))) (SW0 (nat_lit 54)) = true := by
  quickRfl

theorem c5_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [18, 4]
    (SW0 (nat_lit 52))) (SW0 (nat_lit 53)) = true := by
  quickRfl

theorem c5_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 18]
    (SW0 (nat_lit 51))) (SW0 (nat_lit 52)) = true := by
  quickRfl

theorem c5_p10 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 18]
    (SW0 (nat_lit 50))) (SW0 (nat_lit 51)) = true := by
  quickRfl

theorem c5_p11 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 18]
    (SW0 (nat_lit 49))) (SW0 (nat_lit 50)) = true := by
  quickRfl

theorem c5_p12 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 5]
    (SW0 (nat_lit 48))) (SW0 (nat_lit 49)) = true := by
  quickRfl

theorem c5_p13 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 4]
    (SW0 (nat_lit 47))) (SW0 (nat_lit 48)) = true := by
  quickRfl

theorem c5_p14 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 5]
    (SW0 (nat_lit 46))) (SW0 (nat_lit 47)) = true := by
  quickRfl

theorem c5_p15 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 5]
    (SW0 (nat_lit 45))) (SW0 (nat_lit 46)) = true := by
  quickRfl

theorem c5_p16 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 18]
    (SW0 (nat_lit 44))) (SW0 (nat_lit 45)) = true := by
  quickRfl

theorem c5_p17 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [4, 18]
    (SW0 (nat_lit 43))) (SW0 (nat_lit 44)) = true := by
  quickRfl

theorem c5_p18 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 5]
    (SW0 (nat_lit 42))) (SW0 (nat_lit 43)) = true := by
  quickRfl

theorem c5_p19 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [3, 17]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 5))) (SW0 (nat_lit 42)) = true := by
  quickRfl

theorem c5_w : WC (nat_lit 5) = [18, 17] ++ ([5, 3] ++ ([17, 3] ++ ([4, 5] ++ ([4, 5] ++ ([3, 17] ++ ([18, 17] ++ ([5, 17] ++ ([18, 4] ++ ([4, 18] ++ ([3, 18] ++ ([3, 18] ++ ([4, 5] ++ ([3, 4] ++ ([3, 5] ++ ([3, 5] ++ ([3, 18] ++ ([4, 18] ++ ([3, 5] ++ ([3, 17]))))))))))))))))))) := rfl

theorem c5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 5))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 5))) (ST (nat_lit 5)) = true :=
  beq_wordMul_of_eq c5_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c5_p19 c5_p18) c5_p17) c5_p16) c5_p15) c5_p14) c5_p13) c5_p12) c5_p11) c5_p10) c5_p9) c5_p8) c5_p7) c5_p6) c5_p5) c5_p4) c5_p3) c5_p2) c5_p1) c5_p0)

end CFSG.KD.Fi24Ext

end
