module

public import Certificates.Kernel.LocalComp.L34V1.Chk
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34V1

open CFSG.KC.Enum CFSG.KS.Raw

@[expose] noncomputable def tri (a : Nat) : Bool := allN 46 fun b => allN 46 fun c => triK a b c

end CertificateChecks.KernelLC.L34V1

#kon_slices CertificateChecks.KernelLC.L34V1.tri 0 46
#kon_join CertificateChecks.KernelLC.L34V1.triAll CertificateChecks.KernelLC.L34V1.tri 46

end
