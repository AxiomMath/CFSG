module

public import Certificates.Kernel.Sporadic.OddCore.Suz786002K
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000

#kon_slices CertificateChecks.KernelSpor.Suz786002.scSl 0 32

#kon_join CertificateChecks.KernelSpor.Suz786002.scAll
  CertificateChecks.KernelSpor.Suz786002.scSl 32

end
