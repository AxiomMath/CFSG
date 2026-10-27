module

public import Certificates.Kernel.Sporadic.L2.Defs
public import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000
set_option Elab.async false

#kon_slices CertificateChecks.KernelSpor.L2K.grSl 0 18
#kon_slices CertificateChecks.KernelSpor.L2K.teSl 0 6

end
