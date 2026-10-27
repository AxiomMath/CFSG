module

public import Certificates.Data.Kernel.ON8138.Defs
public import Certificates.Kernel.ON8138.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelON8138

open CFSG.KC.ON8138 CFSG.KD.ON8138

theorem leaves6 : spRange R0K TK WK MK 54 9 = true := by quickRfl

theorem leaves7 : spRange R0K TK WK MK 63 9 = true := by quickRfl

theorem leaves8 : spRange R0K TK WK MK 72 9 = true := by quickRfl

end CertificateChecks.KernelON8138

end
