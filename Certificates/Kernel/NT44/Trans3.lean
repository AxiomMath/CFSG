module

public import Certificates.Kernel.NT44.Pack2
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 200

namespace CertificateChecks.KernelNT44

open CFSG.KC.Misc.Clos (allR)

theorem nt44_tr12 : allR 192 16 nt44TrAt = true := by quickRfl
theorem nt44_tr13 : allR 208 16 nt44TrAt = true := by quickRfl
theorem nt44_tr14 : allR 224 16 nt44TrAt = true := by quickRfl
theorem nt44_tr15 : allR 240 16 nt44TrAt = true := by quickRfl

end CertificateChecks.KernelNT44

end
