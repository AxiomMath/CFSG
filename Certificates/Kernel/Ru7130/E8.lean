module

public import Certificates.Kernel.Ru7130.Codes
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.HSA312.Defs

set_option maxRecDepth 100000

public section

namespace CFSG.KD.Ru7130

open CFSG.KC.HSA312

theorem e8 : e8C 4060 12 4095 I Vs Ls CFSG.Quasithin.A312S.Ru.ruVMats = true := by quickRfl

end CFSG.KD.Ru7130

end
