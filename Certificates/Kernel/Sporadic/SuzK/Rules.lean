module

public import Certificates.Kernel.Sporadic.SuzK.TabDefs
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000

#kon_slices CertificateChecks.KernelSpor.SuzK.ruleK 0 16
#kon_slices CertificateChecks.KernelSpor.SuzK.invSl 0 14

end
