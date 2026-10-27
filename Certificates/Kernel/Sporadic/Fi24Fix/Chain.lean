module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Fi24Fix.Data

public section

namespace CFSG.KD.Fi24Fix

open CFSG.KC.Ord CFSG.KC.Fi24Fix CFSG.KD.BrFi24

theorem valid : andB (VLD R) (andB (VLD Y) (andB (VLD Q) (VLD C))) = true := by
  quickRfl

theorem chain : Nat.beq (wordMul MUL RB W R) Y = true := by
  quickRfl

theorem span_le : Nat.beq (MUL Q Y) Y = true := by
  quickRfl

theorem span_ge : Nat.beq (MUL Y C) Q = true := by
  quickRfl

end CFSG.KD.Fi24Fix

end
