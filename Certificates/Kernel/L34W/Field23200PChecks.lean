module

public import Certificates.Data.Kernel.L34W.Field23200P
public import Certificates.Kernel.L34W.Tabs
public import Certificates.Kernel.L34W.Gens
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelL34W

open CFSG.KC.Enum CFSG.KC.L34W

theorem ch23200p_k : fieldP T1X.F GT (GT 4) = true := by quickRfl

theorem ch23200pa_k : alphaZK AlX.F = true := by quickRfl

end CertificateChecks.KernelL34W

end
