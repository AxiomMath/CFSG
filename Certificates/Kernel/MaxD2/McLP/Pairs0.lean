module

public import Certificates.Kernel.MaxD2.McLP.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace CertificateChecks.KernelMaxD2.McLP

open CFSG.KC.Enum CFSG.KS CFSG.KS.MaxD2 CFSG.KS.PEnum

theorem k_np2 : Nat.beq (r32 MISC 1) 1368 = true := by quickRfl
theorem k_pair0 : pairsK 0 = true := by quickRfl
theorem k_pair1 : pairsK 1 = true := by quickRfl
theorem k_pair2 : pairsK 2 = true := by quickRfl
theorem k_pair3 : pairsK 3 = true := by quickRfl
theorem k_pair4 : pairsK 4 = true := by quickRfl
theorem k_pair5 : pairsK 5 = true := by quickRfl
theorem k_pair6 : pairsK 6 = true := by quickRfl
theorem k_pair7 : pairsK 7 = true := by quickRfl
theorem k_pair8 : pairsK 8 = true := by quickRfl
theorem k_pair9 : pairsK 9 = true := by quickRfl

end CertificateChecks.KernelMaxD2.McLP

end
