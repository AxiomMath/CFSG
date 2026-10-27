module

public import Certificates.Kernel.Sporadic.Q3A.Defs
public import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelSpor.Q3AK

theorem kDs0 : dsChk 0 = true := by quickRfl
theorem kDs1 : dsChk 1 = true := by quickRfl
theorem kDs2 : dsChk 2 = true := by quickRfl

end CertificateChecks.KernelSpor.Q3AK

#kon_slices CertificateChecks.KernelSpor.Q3AK.ci0 0 18
#kon_slices CertificateChecks.KernelSpor.Q3AK.ci1 0 4
#kon_slices CertificateChecks.KernelSpor.Q3AK.ci2 0 486
#kon_slices CertificateChecks.KernelSpor.Q3AK.sp0 0 18
#kon_slices CertificateChecks.KernelSpor.Q3AK.sp1 0 4
#kon_slices CertificateChecks.KernelSpor.Q3AK.sp2 0 486

end
