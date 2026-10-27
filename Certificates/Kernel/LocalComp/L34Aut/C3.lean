module

public import Certificates.Kernel.LocalComp.L34Aut.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Aut

theorem k5180c9 : aut5180 135 15 = true := by quickRfl

theorem k5180c10 : aut5180 150 15 = true := by quickRfl

theorem k5180c11 : aut5180 165 15 = true := by quickRfl

end CertificateChecks.KernelLC.L34Aut

end
