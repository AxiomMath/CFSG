module

public import Certificates.Kernel.Sporadic.SuzK.KeyDefs
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzK

set_option Elab.async false

theorem root_ok : rootK = true := by quickRfl

end CertificateChecks.KernelSpor.SuzK

#kon_slices CertificateChecks.KernelSpor.SuzK.sortSl 0 65

end
