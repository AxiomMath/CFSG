module

public import Certificates.Kernel.LocalComp.L34RC.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34RC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CertificateChecks.KernelLC.L34X
open CFSG.KLie.CT (andB orB notB)

theorem k07f0 : fourRows 0 31 = true := by quickRfl

theorem k07f1 : fourRows 31 30 = true := by quickRfl

theorem k07f2 : fourRows 61 30 = true := by quickRfl

end CertificateChecks.KernelLC.L34RC

end
