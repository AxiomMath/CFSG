module

public import Certificates.Kernel.LocalComp.L34Un.Defs
import Certificates.Kernel.Sporadic.ON.Gen
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue

public section

set_option maxRecDepth 400000

#kon_slices CertificateChecks.KernelLC.L34Un.un 0 180
#kon_join CertificateChecks.KernelLC.L34Un.unAll CertificateChecks.KernelLC.L34Un.un 180

end
