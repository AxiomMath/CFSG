module

public import Certificates.Data.Kernel.F7Max.Defs

public section

namespace CFSG.KC.F7Max

set_option maxRecDepth 100000

theorem coverOK_eq : coverOK = true := by decide +kernel

theorem genOK_399 : genOK 399 = true := by decide +kernel

theorem genOK_742 : genOK 742 = true := by decide +kernel

theorem genOK_1134 : genOK 1134 = true := by decide +kernel

end CFSG.KC.F7Max
