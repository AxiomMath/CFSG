
module

public import Certificates.Kernel.Sporadic.ON4.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON4K

theorem heads_ok : headsOK = true := by quickRfl

end CertificateChecks.KernelSpor.ON4K

#kon_slices CertificateChecks.KernelSpor.ON4K.pxS 0 8
#kon_slices CertificateChecks.KernelSpor.ON4K.posCS 0 24
#kon_slices CertificateChecks.KernelSpor.ON4K.ptC0 0 15
#kon_slices CertificateChecks.KernelSpor.ON4K.ptC1 0 21
#kon_slices CertificateChecks.KernelSpor.ON4K.ptC2 0 1
#kon_slices CertificateChecks.KernelSpor.ON4K.sch0 0 15
#kon_slices CertificateChecks.KernelSpor.ON4K.sch1 0 42
#kon_slices CertificateChecks.KernelSpor.ON4K.sch2 0 1
#kon_slices CertificateChecks.KernelSpor.ON4K.tree2 0 36

end
