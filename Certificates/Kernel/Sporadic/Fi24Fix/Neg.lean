module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Fi24Fix.Data
import Certificates.Kernel.Sporadic.Fi24Fix.Chain

public section

set_option Elab.async false

namespace CFSG.KD.Fi24Fix.Neg

open CFSG.KC.Ord CFSG.KC.Fi24Fix CFSG.KD.BrFi24 CFSG.KD.Fi24Fix

theorem keeps8 : notB (keepsOK MUL Q (RB 9)) = true := by quickRfl

theorem keeps_shifted : notB (keepsOK MUL (MUL (RB 9) Q) (RB 1)) = true := by quickRfl

theorem chain_short : notB (Nat.beq (wordMul MUL RB (List.tail W) R) Y) = true :=
  notB_beq_wordMul_of_eq (w' := [] ++ ([6, 16] ++ ([4, 14] ++ ([2, 12] ++ ([21, 11] ++ ([18, 8] ++
    ([14, 7] ++ ([15, 3] ++ ([13, 1] ++ ([10, 14] ++ ([7, 15] ++ ([5, 14] ++ ([4, 13] ++
    ([3, 18] ++ [2, 12])))))))))))))) rfl
    (notB_beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append
      (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append
      (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append
      (beq_wordMul_append (beq_wordMul_append chain_p14 chain_p13) chain_p12) chain_p11)
      chain_p10) chain_p9) chain_p8) chain_p7) chain_p6) chain_p5) chain_p4) chain_p3) chain_p2)
      chain_p1) (by quickRfl))

theorem span_le_flip : notB (Nat.beq (MUL (Nat.xor Q 1) Y) Y) = true := by quickRfl

theorem span_ge_flip : notB (Nat.beq (MUL Y (Nat.xor C 1)) Q) = true := by quickRfl

theorem orbit_long : notB (ascOK S 31672 306936) = true := by quickRfl

theorem orbit_bound : notB (ascOK S 31671 (S 31670)) = true := by quickRfl

end CFSG.KD.Fi24Fix.Neg

end
