module

public import Certificates.Kernel.NT44.Pack2
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 200

namespace CertificateChecks.KernelNT44

open CFSG.KC.Misc.Clos (allR)

theorem nt44_tr4 : allR 64 16 nt44TrAt = true := by quickRfl
theorem nt44_tr5 : allR 80 16 nt44TrAt = true := by quickRfl
theorem nt44_tr6 : allR 96 16 nt44TrAt = true := by quickRfl
theorem nt44_tr7 : allR 112 16 nt44TrAt = true := by quickRfl

end CertificateChecks.KernelNT44

end
