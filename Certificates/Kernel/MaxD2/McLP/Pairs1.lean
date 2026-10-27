module

public import Certificates.Kernel.MaxD2.McLP.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace CertificateChecks.KernelMaxD2.McLP

theorem k_pair10 : pairsK 10 = true := by quickRfl
theorem k_pair11 : pairsK 11 = true := by quickRfl
theorem k_pair12 : pairsK 12 = true := by quickRfl
theorem k_pair13 : pairsK 13 = true := by quickRfl
theorem k_pair14 : pairsK 14 = true := by quickRfl
theorem k_pair15 : pairsK 15 = true := by quickRfl
theorem k_pair16 : pairsK 16 = true := by quickRfl
theorem k_pair17 : pairsK 17 = true := by quickRfl
theorem k_pair18 : pairsK 18 = true := by quickRfl
theorem k_pair19 : pairsK 19 = true := by quickRfl

end CertificateChecks.KernelMaxD2.McLP

end
