module

public import Certificates.Data.Kernel.ON8138.Defs
public import Certificates.Kernel.ON8138.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelON8138

open CFSG.KC.ON8138 CFSG.KD.ON8138

theorem leaves3 : spRange R0K TK WK MK 27 9 = true := by quickRfl

theorem leaves4 : spRange R0K TK WK MK 36 9 = true := by quickRfl

theorem leaves5 : spRange R0K TK WK MK 45 9 = true := by quickRfl

end CertificateChecks.KernelON8138

end
