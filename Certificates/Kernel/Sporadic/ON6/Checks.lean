module

public import Certificates.Kernel.Sporadic.ON6.Defs
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON6K

theorem tSmall_ok : tSmall = true := by quickRfl
theorem mSmall_ok : mSmall = true := by quickRfl
theorem lSmall_ok : lSmall = true := by quickRfl
theorem pSmall_ok : pSmall = true := by quickRfl
theorem qSmall_ok : qSmall = true := by quickRfl

end CertificateChecks.KernelSpor.ON6K

#kon_slices CertificateChecks.KernelSpor.ON6K.tSch 0 12
#kon_slices CertificateChecks.KernelSpor.ON6K.pSch 0 28

end
