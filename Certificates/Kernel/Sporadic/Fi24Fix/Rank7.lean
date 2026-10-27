module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Fi24Fix.DataK

public section

namespace CFSG.KD.Fi24Fix

open CFSG.KC.Fi24FixK

theorem clos7 : closOK S IX TG (nat_lit 31671) (nat_lit 28672) (nat_lit 2999) (nat_lit 47) = true := by
  quickRfl

theorem cnt7 : Nat.beq (cntFix S TG PW AW (nat_lit 28672) (nat_lit 2999) (nat_lit 47)) (nat_lit 41) =
    true := by
  quickRfl

end CFSG.KD.Fi24Fix

end
