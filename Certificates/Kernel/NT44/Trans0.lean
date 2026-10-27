module

public import Certificates.Kernel.NT44.Pack2
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 200

namespace CertificateChecks.KernelNT44

open CFSG.KC.Misc.Clos (allR)

theorem nt44_tr0 : allR 0 16 nt44TrAt = true := by quickRfl
theorem nt44_tr1 : allR 16 16 nt44TrAt = true := by quickRfl
theorem nt44_tr2 : allR 32 16 nt44TrAt = true := by quickRfl
theorem nt44_tr3 : allR 48 16 nt44TrAt = true := by quickRfl

end CertificateChecks.KernelNT44

end
