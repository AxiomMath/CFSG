module

public import Certificates.Kernel.J4Ov.Defs4206
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Ov

open CFSG.KC.J4Q

#j4q_all CertificateChecks.KernelJ4Ov.ch4206S CertificateChecks.KernelJ4Ov.so4206 441

theorem dist5_4206 : distK 0 28 15180 = true := by quickRfl

theorem dist6_4206 : distK 28 21 28336 = true := by quickRfl

theorem shape4206_ok : shape4206 = true := by quickRfl

theorem letters4206_ok : lettersK = true := by quickRfl

theorem roots4206_ok : rootsK = true := by quickRfl

end CertificateChecks.KernelJ4Ov

end
