module

public import Certificates.Kernel.EvenBN.Th8D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Th8

open CFSG.KC.M1F2

theorem k8 : Nat.beq (x8 A.M B.M) (idF 248) = true := by quickRfl

theorem k4 : moves0 (x4 A.M B.M) = true := by quickRfl

end CertificateChecks.Th8

end
