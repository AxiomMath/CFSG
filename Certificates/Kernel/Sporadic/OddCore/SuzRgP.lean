module

public import Certificates.Kernel.Sporadic.OddCore.SuzRgS
public import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000
set_option Elab.async false

#kon_slices CertificateChecks.KernelSpor.SuzRg.ptSl 0 16
#kon_slices CertificateChecks.KernelSpor.SuzRg.ucSl 0 16
#kon_slices CertificateChecks.KernelSpor.SuzRg.bfSl 0 81
#kon_slices CertificateChecks.KernelSpor.SuzRg.irK 0 64

end
