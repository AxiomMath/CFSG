module

public import Certificates.Data.Kernel.ON8138.Defs
public import Certificates.Kernel.ON8138.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelON8138

open CFSG.KC.ON8138 CFSG.KD.ON8138

theorem leaves0 : spRange R0K TK WK MK 0 9 = true := by quickRfl

theorem leaves1 : spRange R0K TK WK MK 9 9 = true := by quickRfl

theorem leaves2 : spRange R0K TK WK MK 18 9 = true := by quickRfl

end CertificateChecks.KernelON8138

end
