module

public import Certificates.Kernel.MaxD2.McLP.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace CertificateChecks.KernelMaxD2.McLP

theorem k_pair20 : pairsK 20 = true := by quickRfl
theorem k_pair21 : pairsK 21 = true := by quickRfl
theorem k_pair22 : pairsK 22 = true := by quickRfl
theorem k_pair23 : pairsK 23 = true := by quickRfl
theorem k_pair24 : pairsK 24 = true := by quickRfl
theorem k_pair25 : pairsK 25 = true := by quickRfl
theorem k_pair26 : pairsK 26 = true := by quickRfl
theorem k_pair27 : pairsK 27 = true := by quickRfl
theorem k_pair28 : pairsK 28 = true := by quickRfl

end CertificateChecks.KernelMaxD2.McLP

end
