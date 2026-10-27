module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Fi24Fix.DataK

public section

namespace CFSG.KD.Fi24Fix

open CFSG.KC.Ord CFSG.KC.Fi24FixK

theorem rootA : Nat.beq (walk TG AW (walk TG PW (nat_lit 0))) (walk TG PW (S (nat_lit 1479))) =
    true := by
  quickRfl

theorem rootA_neg_prev : notB (Nat.beq (walk TG AW (walk TG PW (nat_lit 0)))
    (walk TG PW (S (nat_lit 1478)))) = true := by
  quickRfl

theorem rootA_neg_next : notB (Nat.beq (walk TG AW (walk TG PW (nat_lit 0)))
    (walk TG PW (S (nat_lit 1480)))) = true := by
  quickRfl

theorem rootA_neg_fix : notB (Nat.beq (walk TG AW (walk TG PW (nat_lit 0)))
    (walk TG PW (nat_lit 0))) = true := by
  quickRfl

end CFSG.KD.Fi24Fix

end
