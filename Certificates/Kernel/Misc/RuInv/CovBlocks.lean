module

public import Certificates.Kernel.Misc.RuInv.Gens
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option Elab.async false

#kon_slices CertificateChecks.KernelMisc.RuInv.covB 0 64
#kon_join CertificateChecks.KernelMisc.RuInv.covAll CertificateChecks.KernelMisc.RuInv.covB 64

end
