
module

public import Certificates.Kernel.Sporadic.ON3.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON3

theorem heads_ok : headsOK = true := by quickRfl

theorem sifts_ok : siftsOK = true := by quickRfl

end CertificateChecks.KernelSpor.ON3

#kon_slices CertificateChecks.KernelSpor.ON3.posS 0 72
#kon_slices CertificateChecks.KernelSpor.ON3.ptT0 0 8
#kon_slices CertificateChecks.KernelSpor.ON3.ptT1 0 1
#kon_slices CertificateChecks.KernelSpor.ON3.ptT2 0 1
#kon_slices CertificateChecks.KernelSpor.ON3.ptM0 0 15
#kon_slices CertificateChecks.KernelSpor.ON3.ptM2 0 1
#kon_slices CertificateChecks.KernelSpor.ON3.ptL0 0 15
#kon_slices CertificateChecks.KernelSpor.ON3.ptL2 0 1

end
