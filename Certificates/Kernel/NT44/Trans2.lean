module

public import Certificates.Kernel.NT44.Pack2
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 200

namespace CertificateChecks.KernelNT44

open CFSG.KC.Misc.Clos (allR)

theorem nt44_tr8 : allR 128 16 nt44TrAt = true := by quickRfl
theorem nt44_tr9 : allR 144 16 nt44TrAt = true := by quickRfl
theorem nt44_tr10 : allR 160 16 nt44TrAt = true := by quickRfl
theorem nt44_tr11 : allR 176 16 nt44TrAt = true := by quickRfl

end CertificateChecks.KernelNT44

end
