module

public import Certificates.Kernel.Sporadic.OddCore.SuzGlA
public import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000
set_option Elab.async false

#kon_slices CertificateChecks.KernelSpor.SuzGl.autSl 0 31

end
