module

public import Certificates.Kernel.He7030.Defs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.He7030

theorem ord3 : ordChk 3 = true := by quickRfl

theorem ord4 : ordChk 4 = true := by quickRfl

theorem norm3 : normChk 3 = true := by quickRfl

theorem norm4 : normChk 4 = true := by quickRfl

theorem lab3 : labChk 3 = true := by quickRfl

theorem lab4 : labChk 4 = true := by quickRfl

end CFSG.KD.He7030

end
