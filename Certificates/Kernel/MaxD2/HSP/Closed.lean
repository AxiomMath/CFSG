module

public import Certificates.Kernel.MaxD2.HSP.Enum
public import Certificates.Kernel.MaxD2.HSP.Data
public import Certificates.Data.Kernel.MaxD2.Closed
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace CertificateChecks.KernelMaxD2.HSP

open CFSG.KC.Enum CFSG.KS CFSG.KS.MaxD2 CFSG.KS.PEnum

theorem k_clos1 : allN NE.cnt (fun k => closK 100 7 NE.cnt NE.T (REP 1) (REPI 1) k (r32 X1 k)) =
    true := by quickRfl
theorem k_clos2 : allN NE.cnt (fun k => closK 100 7 NE.cnt NE.T (REP 2) (REPI 2) k (r32 X2 k)) =
    true := by quickRfl

end CertificateChecks.KernelMaxD2.HSP

end
