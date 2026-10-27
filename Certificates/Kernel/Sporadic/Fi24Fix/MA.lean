module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Fi24Br.Data

public section

namespace CFSG.KD.Fi24Fix

open CFSG.KD.BrFi24

theorem mA_regs : Nat.beq (MUL (RB 8) (RB 11)) (RB 23) = true := by
  quickRfl

end CFSG.KD.Fi24Fix

end
