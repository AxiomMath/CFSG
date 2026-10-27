module

public import Certificates.Kernel.Sporadic.OddCore.SuzGlS
public import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000
set_option Elab.async false

#kon_slices CertificateChecks.KernelSpor.SuzGl.idxSl 16 32

end
