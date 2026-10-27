module

public import Certificates.Kernel.SimsF5.Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSimsF5

open CFSG.KC.Ord CFSG.KC.SimsF5

set_option maxRecDepth 100000

theorem ch7600t : tOK = true := by quickRfl

theorem ch7600u : uOK = true := by quickRfl

#kc_each ch7600m0 0 5

theorem ch7600mA : memOK 1 3 0 = true := by quickRfl

theorem ch7600mB : memOK 2 3 3 = true := by quickRfl

theorem ch7600mM1 : memOK 3 9 6 = true := by quickRfl

theorem ch7600mM2 : memOK 4 15 15 = true := by quickRfl

theorem ch7600sA : subOK 1 3 1 0 0 0 = true := by quickRfl

theorem ch7600sB : subOK 2 3 1 3 3 1 = true := by quickRfl

theorem ch7600sM1 : subOK 3 9 2 6 6 2 = true := by quickRfl

theorem ch7600sM2a : subOK 4 3 1 15 24 4 = true := by quickRfl

theorem ch7600sM2b : subOK 4 5 1 18 27 5 = true := by quickRfl

theorem ch7600sM0 : subOK 5 81 4 23 32 6 = true := by quickRfl

theorem ch7600rep : repOK = true := by quickRfl

theorem ch7600join : joinOK = true := by quickRfl

theorem ch7600inc : incOK = true := by quickRfl

theorem ch7600not : notOK = true := by quickRfl

end CertificateChecks.KernelSimsF5

end
