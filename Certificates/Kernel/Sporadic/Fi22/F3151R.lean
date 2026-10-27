
module

public import Certificates.Kernel.Sporadic.Fi22.F3151D
public import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kon_slices CertificateChecks.KernelSpor.Fi22F2.treeSl 0 7

#kon_slices CertificateChecks.KernelSpor.Fi22F2.rootSl 0 9

#kon_slices CertificateChecks.KernelSpor.Fi22F2.hSl 0 9

namespace CertificateChecks.KernelSpor.Fi22F2

open CFSG.KC.Enum CFSG.KS CertificateChecks.KernelSpor

theorem zE : bAnd(Nat.beq (Fi22LabX.O6 2) Fi22E2073.E, Fi22X.cn Fi22E2073.E) = true := by quickRfl

theorem tpOK : tpK = true := by quickRfl

end CertificateChecks.KernelSpor.Fi22F2

end
