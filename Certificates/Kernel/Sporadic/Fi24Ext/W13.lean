module

public import Certificates.Kernel.Sporadic.Fi24Ext.Chunks
public import Certificates.Kernel.Sporadic.Fi24Fix.Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree CFSG.KD.Fi24Ext SW13 "Certificates/Kernel/Sporadic/Fi24Ext/data/w13.bin" 152491 4 1372419 12732306018550527512

public section

set_option Elab.async false

open CFSG.KC.Fi24Fix (beq_wordMul_append beq_wordMul_of_eq)

namespace CFSG.KD.Fi24Ext

theorem c54_p0 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 13]
    (SW13 (nat_lit 8))) (ST (nat_lit 54)) = true := by
  quickRfl

theorem c54_p1 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [21, 5]
    (SW13 (nat_lit 7))) (SW13 (nat_lit 8)) = true := by
  quickRfl

theorem c54_p2 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [28, 12]
    (SW13 (nat_lit 6))) (SW13 (nat_lit 7)) = true := by
  quickRfl

theorem c54_p3 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [20, 26]
    (SW13 (nat_lit 5))) (SW13 (nat_lit 6)) = true := by
  quickRfl

theorem c54_p4 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [27, 11]
    (SW13 (nat_lit 4))) (SW13 (nat_lit 5)) = true := by
  quickRfl

theorem c54_p5 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 10]
    (SW13 (nat_lit 3))) (SW13 (nat_lit 4)) = true := by
  quickRfl

theorem c54_p6 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [5, 22]
    (SW13 (nat_lit 2))) (SW13 (nat_lit 3)) = true := by
  quickRfl

theorem c54_p7 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [23, 9]
    (SW13 (nat_lit 1))) (SW13 (nat_lit 2)) = true := by
  quickRfl

theorem c54_p8 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [19, 10]
    (SW13 (nat_lit 0))) (SW13 (nat_lit 1)) = true := by
  quickRfl

theorem c54_p9 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG [8, 12]
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 54))) (SW13 (nat_lit 0)) = true := by
  quickRfl

theorem c54_w : WC (nat_lit 54) = [8, 13] ++ ([21, 5] ++ ([28, 12] ++ ([20, 26] ++ ([27, 11] ++ ([23, 10] ++ ([5, 22] ++ ([23, 9] ++ ([19, 10] ++ ([8, 12]))))))))) := rfl

theorem c54 : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC (nat_lit 54))
    (CFSG.KC.Fi24Ext.chunkIn FS ST CFSG.KD.BrFi24.ONE (nat_lit 54))) (ST (nat_lit 54)) = true :=
  beq_wordMul_of_eq c54_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c54_p9 c54_p8) c54_p7) c54_p6) c54_p5) c54_p4) c54_p3) c54_p2) c54_p1) c54_p0)

end CFSG.KD.Fi24Ext

end
