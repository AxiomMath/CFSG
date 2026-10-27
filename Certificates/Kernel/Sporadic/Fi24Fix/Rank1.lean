module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Fi24Fix.DataK

public section

namespace CFSG.KD.Fi24Fix

open CFSG.KC.Fi24FixK

theorem clos1 : closOK S IX TG (nat_lit 31671) (nat_lit 4096) (nat_lit 4096) (nat_lit 64) = true := by
  quickRfl

theorem cnt1 : Nat.beq (cntFix S TG PW AW (nat_lit 4096) (nat_lit 4096) (nat_lit 64)) (nat_lit 29) =
    true := by
  quickRfl

end CFSG.KD.Fi24Fix

end
