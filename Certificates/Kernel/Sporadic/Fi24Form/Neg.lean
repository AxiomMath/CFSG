module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Fi24Form.Checks

public section

namespace CFSG.KD.Fi24Form

open CFSG.KC.Fi24Form

open CFSG.KC.Ord (notB)

theorem ng_b : notB (transM (CFSG.KD.BrFi24.RB 24) (CFSG.KD.BrFi24.RB 24) 0 196 4) = true := by
  quickRfl

theorem ng_fb : notB (transM FB FB 0 196 4) = true := by quickRfl

theorem ng_fa : notB (transM FA CFSG.KD.Fi24Ext.F 0 196 4) = true := by quickRfl

end CFSG.KD.Fi24Form

end
