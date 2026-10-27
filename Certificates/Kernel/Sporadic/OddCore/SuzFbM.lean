module

public import Certificates.Kernel.Sporadic.OddCore.SuzFbS
public import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000
set_option Elab.async false

#kon_slices CertificateChecks.KernelSpor.SuzFb.invSl 0 16
#kon_slices CertificateChecks.KernelSpor.SuzFb.liftSl 0 13
#kon_slices CertificateChecks.KernelSpor.SuzFb.qeSl 0 26
#kon_slices CertificateChecks.KernelSpor.SuzFb.conjNeg 0 76

end
