module

public import Certificates.Kernel.LocalComp.L34Aut.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Aut

theorem k5180c3 : aut5180 45 15 = true := by quickRfl

theorem k5180c4 : aut5180 60 15 = true := by quickRfl

theorem k5180c5 : aut5180 75 15 = true := by quickRfl

end CertificateChecks.KernelLC.L34Aut

end
