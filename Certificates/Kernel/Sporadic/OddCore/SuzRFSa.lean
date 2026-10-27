module

public import Certificates.Kernel.Sporadic.OddCore.SuzRFS
public import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000
set_option Elab.async false

#kon_slices CertificateChecks.KernelSpor.SuzRF.sSl 0 128

end
