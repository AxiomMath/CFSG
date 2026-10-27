module

public import Certificates.Kernel.LocalComp.L34Aut.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Aut

theorem k5180c6 : aut5180 90 15 = true := by quickRfl

theorem k5180c7 : aut5180 105 15 = true := by quickRfl

theorem k5180c8 : aut5180 120 15 = true := by quickRfl

end CertificateChecks.KernelLC.L34Aut

end
