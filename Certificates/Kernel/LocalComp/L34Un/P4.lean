module

public import Certificates.Kernel.LocalComp.L34Un.Defs
import Certificates.Kernel.Sporadic.ON.Gen
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue

public section

set_option maxRecDepth 400000

#kon_slices CertificateChecks.KernelLC.L34Un.ck4 0 32
#kon_join CertificateChecks.KernelLC.L34Un.ck4All CertificateChecks.KernelLC.L34Un.ck4 32

end
