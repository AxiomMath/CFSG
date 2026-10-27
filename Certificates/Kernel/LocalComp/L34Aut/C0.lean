module

public import Certificates.Kernel.LocalComp.L34Aut.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Aut

theorem k5180aux : aux5180 = true := by quickRfl

theorem k5180c0 : aut5180 0 15 = true := by quickRfl

theorem k5180c1 : aut5180 15 15 = true := by quickRfl

theorem k5180c2 : aut5180 30 15 = true := by quickRfl

end CertificateChecks.KernelLC.L34Aut

end
