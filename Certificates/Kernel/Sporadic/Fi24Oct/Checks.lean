module

public import Certificates.Kernel.Sporadic.Fi24Oct.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Fi24Oct.Ck

open CFSG.KD.Fi24Oct

theorem rt_t : rt = true := by quickRfl

theorem cm_t : cm = true := by quickRfl

theorem pr_t : pr = true := by quickRfl

theorem nm0_t : nm (nat_lit 0) = true := by quickRfl

theorem nm1_t : nm (nat_lit 1) = true := by quickRfl

theorem pd_t : pd = true := by quickRfl

end CFSG.KD.Fi24Oct.Ck

end
