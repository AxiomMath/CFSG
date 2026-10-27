module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Fi24Fix.Data

public section

namespace CFSG.KD.Fi24Fix

open CFSG.KC.Ord CFSG.KC.Fi24Fix CFSG.KD.BrFi24

theorem keeps0 : keepsOK MUL Q (RB 1) = true := by quickRfl

theorem keeps1 : keepsOK MUL Q (RB 2) = true := by quickRfl

theorem keeps2 : keepsOK MUL Q (RB 3) = true := by quickRfl

theorem keeps3 : keepsOK MUL Q (RB 4) = true := by quickRfl

theorem keeps4 : keepsOK MUL Q (RB 5) = true := by quickRfl

theorem keeps5 : keepsOK MUL Q (RB 6) = true := by quickRfl

theorem keeps6 : keepsOK MUL Q (RB 7) = true := by quickRfl

theorem keeps7 : keepsOK MUL Q (RB 8) = true := by quickRfl

theorem keeps9 : keepsOK MUL Q (RB 10) = true := by quickRfl

end CFSG.KD.Fi24Fix

end
