module

public import Certificates.Kernel.Sporadic.OddCore.SuzRFS
public import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000
set_option Elab.async false

#kon_slices CertificateChecks.KernelSpor.SuzRF.oSl0 0 1
#kon_slices CertificateChecks.KernelSpor.SuzRF.oSl1 0 9
#kon_slices CertificateChecks.KernelSpor.SuzRF.oSl2 0 60
#kon_slices CertificateChecks.KernelSpor.SuzRF.wSl 0 256
#kon_slices CertificateChecks.KernelSpor.SuzRF.pSl 0 32
#kon_slices CertificateChecks.KernelSpor.SuzRF.genK 0 10

end
