module

public import Certificates.Kernel.MaxD2.HSOver.Enum
public import Certificates.Kernel.MaxD2.HSOver.Data
public import Certificates.Data.Kernel.MaxD2.Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace CertificateChecks.KernelMaxD2.HSOver

open CFSG.KC.Enum CFSG.KS CFSG.KS.MaxD2 CFSG.KS.PEnum

theorem rep_t0 : allN 7 (fun d => repK 100 7 3 21 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 1 d)) = true := by quickRfl
theorem rep_t1 : allN 7 (fun d => repK 100 7 3 21 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 8 d)) = true := by quickRfl

end CertificateChecks.KernelMaxD2.HSOver

end
