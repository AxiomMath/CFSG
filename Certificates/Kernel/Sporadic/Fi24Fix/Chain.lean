module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24Fix.Data
public import Certificates.Kernel.Sporadic.Fi24Fix.Split

#kc_repo #kc_ktree CFSG.KD.Fi24Fix SCH "Certificates/Kernel/Sporadic/Fi24Fix/data/chain.bin" 152491 4 2134874 465529326554065283

public section

set_option Elab.async false

namespace CFSG.KD.Fi24Fix

open CFSG.KC.Ord CFSG.KC.Fi24Fix CFSG.KD.BrFi24

theorem valid : andB (VLD R) (andB (VLD Y) (andB (VLD Q) (VLD C))) = true := by
  quickRfl

theorem chain_p0 : Nat.beq (wordMul MUL RB [20] (SCH (nat_lit 13))) Y = true := by
  quickRfl

theorem chain_p1 : Nat.beq (wordMul MUL RB [6, 16] (SCH (nat_lit 12))) (SCH (nat_lit 13)) =
    true := by
  quickRfl

theorem chain_p2 : Nat.beq (wordMul MUL RB [4, 14] (SCH (nat_lit 11))) (SCH (nat_lit 12)) =
    true := by
  quickRfl

theorem chain_p3 : Nat.beq (wordMul MUL RB [2, 12] (SCH (nat_lit 10))) (SCH (nat_lit 11)) =
    true := by
  quickRfl

theorem chain_p4 : Nat.beq (wordMul MUL RB [21, 11] (SCH (nat_lit 9))) (SCH (nat_lit 10)) =
    true := by
  quickRfl

theorem chain_p5 : Nat.beq (wordMul MUL RB [18, 8] (SCH (nat_lit 8))) (SCH (nat_lit 9)) =
    true := by
  quickRfl

theorem chain_p6 : Nat.beq (wordMul MUL RB [14, 7] (SCH (nat_lit 7))) (SCH (nat_lit 8)) =
    true := by
  quickRfl

theorem chain_p7 : Nat.beq (wordMul MUL RB [15, 3] (SCH (nat_lit 6))) (SCH (nat_lit 7)) =
    true := by
  quickRfl

theorem chain_p8 : Nat.beq (wordMul MUL RB [13, 1] (SCH (nat_lit 5))) (SCH (nat_lit 6)) =
    true := by
  quickRfl

theorem chain_p9 : Nat.beq (wordMul MUL RB [10, 14] (SCH (nat_lit 4))) (SCH (nat_lit 5)) =
    true := by
  quickRfl

theorem chain_p10 : Nat.beq (wordMul MUL RB [7, 15] (SCH (nat_lit 3))) (SCH (nat_lit 4)) =
    true := by
  quickRfl

theorem chain_p11 : Nat.beq (wordMul MUL RB [5, 14] (SCH (nat_lit 2))) (SCH (nat_lit 3)) =
    true := by
  quickRfl

theorem chain_p12 : Nat.beq (wordMul MUL RB [4, 13] (SCH (nat_lit 1))) (SCH (nat_lit 2)) =
    true := by
  quickRfl

theorem chain_p13 : Nat.beq (wordMul MUL RB [3, 18] (SCH (nat_lit 0))) (SCH (nat_lit 1)) =
    true := by
  quickRfl

theorem chain_p14 : Nat.beq (wordMul MUL RB [2, 12] R) (SCH (nat_lit 0)) = true := by
  quickRfl

theorem chain_w : W = [20] ++ ([6, 16] ++ ([4, 14] ++ ([2, 12] ++ ([21, 11] ++ ([18, 8] ++
    ([14, 7] ++ ([15, 3] ++ ([13, 1] ++ ([10, 14] ++ ([7, 15] ++ ([5, 14] ++ ([4, 13] ++
    ([3, 18] ++ [2, 12]))))))))))))) := rfl

theorem chain : Nat.beq (wordMul MUL RB W R) Y = true :=
  beq_wordMul_of_eq chain_w (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append chain_p14 chain_p13) chain_p12)
    chain_p11) chain_p10) chain_p9) chain_p8) chain_p7) chain_p6) chain_p5) chain_p4) chain_p3)
    chain_p2) chain_p1) chain_p0)

theorem span_le : Nat.beq (MUL Q Y) Y = true := by
  quickRfl

theorem span_ge : Nat.beq (MUL Y C) Q = true := by
  quickRfl

end CFSG.KD.Fi24Fix

end
