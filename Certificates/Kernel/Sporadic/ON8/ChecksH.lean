module

public import Certificates.Kernel.Sporadic.ON8.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.ON5.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON8

theorem h_dist : hDist = true := by quickRfl

end CertificateChecks.KernelSpor.ON8

#kon_slices CertificateChecks.KernelSpor.ON8.hSl 0 9
#kon_slices CertificateChecks.KernelSpor.ON8.tSl 0 9

end
