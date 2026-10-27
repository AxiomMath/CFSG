module

public import Certificates.Kernel.U42Lat.Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelU42Lat

set_option maxRecDepth 100000

theorem ch409001t : tOK = true := by quickRfl

theorem ch409001u : uOK = true := by quickRfl

#kc_each ch409001m 0 3

theorem ch409001L1 : memOK 1 3 0 = true := by quickRfl

theorem ch409001L2 : memOK 2 3 3 = true := by quickRfl

theorem ch409001L3 : memOK 3 9 6 = true := by quickRfl

theorem ch409001L4 : memOK 4 15 15 = true := by quickRfl

theorem ch409001s1 : subOK 1 3 1 0 0 0 = true := by quickRfl

theorem ch409001s2 : subOK 2 3 1 3 3 1 = true := by quickRfl

theorem ch409001s3 : subOK 3 9 2 6 6 2 = true := by quickRfl

theorem ch409001s4a : subOK 4 3 1 15 24 4 = true := by quickRfl

theorem ch409001s4b : subOK 4 5 1 18 27 5 = true := by quickRfl

theorem ch409001sM81 : subOK 6 81 3 23 32 6 = true := by quickRfl

theorem ch409001sM5 : subOK 6 5 1 104 275 9 = true := by quickRfl

theorem ch409001rep : repOK = true := by quickRfl

theorem ch409001join : joinOK = true := by quickRfl

theorem ch409001inc : incOK = true := by quickRfl

theorem ch409001d0 : d0OK = true := by quickRfl

end CertificateChecks.KernelU42Lat

end
