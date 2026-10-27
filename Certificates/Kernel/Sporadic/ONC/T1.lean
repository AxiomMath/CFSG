module

public import Certificates.Kernel.Sporadic.ONC.Defs
public import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000

#kon_slices CertificateChecks.KernelSpor.ONC.tr1 0 12
#kon_slices CertificateChecks.KernelSpor.ONC.tr2 0 1
#kon_slices CertificateChecks.KernelSpor.ONC.tr3 0 1
#kon_slices CertificateChecks.KernelSpor.ONC.tr4 0 6
#kon_slices CertificateChecks.KernelSpor.ONC.tr7 0 7

end
