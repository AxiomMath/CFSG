module

public import Certificates.Kernel.LocalComp.L34T3.Defs30
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.LocalComp.L34T3.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34T3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CertificateChecks.KernelLC.L34X
open CFSG.KLie.CT (andB notB)

theorem k30c0 : chunk45 unit23230 0 = true := by quickRfl

theorem k30c1 : chunk45 unit23230 1 = true := by quickRfl

theorem k30d : allN 9 (fun i => canonK 42 6 (mask 6) (42 * 6) (L34D2.P i)) = true := by quickRfl

theorem k30c : allN 72 (fun i => canonK 42 6 (mask 6) (42 * 6) (L34C4.P i)) = true := by quickRfl

end CertificateChecks.KernelLC.L34T3

end
