module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Fi24Fix.DataK
public import Certificates.Kernel.Sporadic.Fi24Fix.DataI

public section

namespace CFSG.KD.Fi24Fix

open CFSG.KC.Fi24FixK

theorem init_digits : digitsOK CT (nat_lit 33396) IA.chars (nat_lit 0) = true := by
  quickRfl

theorem init_cols : colsOK R1 R2 CT = true := by
  quickRfl

theorem init_rows : rowsZOK R1 R2 = true := by
  quickRfl

end CFSG.KD.Fi24Fix

end
