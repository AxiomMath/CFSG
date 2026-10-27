module

public import Certificates.Kernel.Sporadic.L2C.Defs
public import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

#kon_slices CertificateChecks.KernelSpor.L2CK.baseSl 0 9
#kon_slices CertificateChecks.KernelSpor.L2CK.liftSl 0 9
#kon_slices CertificateChecks.KernelSpor.L2CK.walkSl 0 10

namespace CertificateChecks.KernelSpor.L2CK

theorem kWord : wordK = true := by quickRfl

theorem kLoc : locK = true := by quickRfl

end CertificateChecks.KernelSpor.L2CK

end
