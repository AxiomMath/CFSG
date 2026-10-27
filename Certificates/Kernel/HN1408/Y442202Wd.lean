module

public import Certificates.Kernel.HN1408.Y442202Inst
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Y442202

theorem ch442202_gens : gensOK = true := by quickRfl

theorem ch442202_w0 : wdK (nat_lit 0) (nat_lit 8) = true := by quickRfl

theorem ch442202_w8 : wdK (nat_lit 8) (nat_lit 64) = true := by quickRfl

end CFSG.KD.HN1408.Y442202

end
