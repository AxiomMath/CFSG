module

public import Certificates.Kernel.Sporadic.OddCore.SuzK0
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000

#kon_slices CertificateChecks.KernelSpor.SuzK0.scSl 0 32

#kon_join CertificateChecks.KernelSpor.SuzK0.scAll CertificateChecks.KernelSpor.SuzK0.scSl 32

end
