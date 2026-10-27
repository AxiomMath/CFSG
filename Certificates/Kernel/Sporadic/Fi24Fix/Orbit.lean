module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Fi24Fix.Data

public section

namespace CFSG.KD.Fi24Fix

open CFSG.KC.Fi24Fix

theorem orbit_asc : ascOK S 31671 306936 = true := by
  quickRfl

end CFSG.KD.Fi24Fix

end
