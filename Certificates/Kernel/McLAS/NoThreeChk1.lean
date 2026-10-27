module

public import Certificates.Kernel.McLAS.NoThreeData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLAS

open CFSG.KC.Enum

theorem noThr_chk1 : allN 1232 (noThrK 1) = true := by quickRfl

end CertificateChecks.KernelMcLAS

end
