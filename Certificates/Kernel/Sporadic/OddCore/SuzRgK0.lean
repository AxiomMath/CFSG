module

public import Certificates.Kernel.Sporadic.OddCore.SuzRgS
public import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000
set_option Elab.async false

#kon_slices CertificateChecks.KernelSpor.SuzRg.cellSl 0 64

end
