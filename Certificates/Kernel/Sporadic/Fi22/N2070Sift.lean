module

public import Certificates.Kernel.Sporadic.Fi22.X2069Final
public import Certificates.Kernel.Sporadic.Fi22.E2065
public import Certificates.Kernel.Sporadic.Fi22.E2067
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.N2070

open CFSG.KC.Enum CFSG.KS.Raw CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22X

theorem cnC : cn (Fi22CentT.L 79) = true := by quickRfl
theorem cnT1 : cn (Fi22ExtT.L 22) = true := by quickRfl
theorem sC : bIf(siftP (Fi22CentT.L 79), false, true) = true := by quickRfl
theorem sUC : siftP (c GO (Fi22CentT.L 79)) = true := by quickRfl
theorem comm : Nat.beq (c (Fi22CentT.L 79) (Fi22ExtT.L 22)) (c (Fi22ExtT.L 22) (Fi22CentT.L 79)) =
    true := by quickRfl

end CertificateChecks.KernelSpor.N2070

end
