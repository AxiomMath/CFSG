module

public import Certificates.Kernel.Fi22Nine.Defs
public import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000

#kon_slices CertificateChecks.KernelSpor.Fi22Nine.centSl 0 32
#kon_join CertificateChecks.KernelSpor.Fi22Nine.centAll CertificateChecks.KernelSpor.Fi22Nine.centSl 32

end
