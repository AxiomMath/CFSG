module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Fi24Fix.Data

public section

namespace CFSG.KD.Fi24Fix.Neg

open CFSG.KC.Ord CFSG.KC.Fi24Fix CFSG.KD.BrFi24 CFSG.KD.Fi24Fix

theorem keeps8 : notB (keepsOK MUL Q (RB 9)) = true := by quickRfl

theorem keeps_shifted : notB (keepsOK MUL (MUL (RB 9) Q) (RB 1)) = true := by quickRfl

theorem chain_short : notB (Nat.beq (wordMul MUL RB (List.tail W) R) Y) = true := by quickRfl

theorem span_le_flip : notB (Nat.beq (MUL (Nat.xor Q 1) Y) Y) = true := by quickRfl

theorem span_ge_flip : notB (Nat.beq (MUL Y (Nat.xor C 1)) Q) = true := by quickRfl

theorem orbit_long : notB (ascOK S 31672 306936) = true := by quickRfl

theorem orbit_bound : notB (ascOK S 31671 (S 31670)) = true := by quickRfl

end CFSG.KD.Fi24Fix.Neg

end
