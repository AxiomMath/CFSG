module

public import Certificates.Kernel.MaxD2.McLP.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace CertificateChecks.KernelMaxD2.McLP

open CFSG.KC.Enum CFSG.KS CFSG.KS.MaxD2 CFSG.KS.PEnum

theorem rep_t0 : repsK 1 29 = true := by quickRfl
theorem rep_t1 : repsK 30 29 = true := by quickRfl
theorem rep_t2 : repsK 59 29 = true := by quickRfl
theorem rep_t3 : repsK 88 26 = true := by quickRfl

end CertificateChecks.KernelMaxD2.McLP

end
