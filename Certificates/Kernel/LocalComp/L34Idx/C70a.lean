module

public import Certificates.Kernel.LocalComp.L34Idx.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.LocalComp.L34T3.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Idx

open CertificateChecks.KernelLC.L34T3

theorem k70c0 : chunk45 idx22970 0 = true := by quickRfl

theorem k70c1 : chunk45 idx22970 1 = true := by quickRfl

end CertificateChecks.KernelLC.L34Idx

end
