module

public import Certificates.Kernel.Misc.RuInv.Gens
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option Elab.async false

#kon_slices CertificateChecks.KernelMisc.RuInv.hashB 0 87
#kon_join CertificateChecks.KernelMisc.RuInv.hashAll CertificateChecks.KernelMisc.RuInv.hashB 87

end
