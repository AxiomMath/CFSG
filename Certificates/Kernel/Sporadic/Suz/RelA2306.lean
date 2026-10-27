module

public import Certificates.Kernel.Sporadic.Suz.Imgs2306
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Suz2306

open CFSG.KC.Enum CFSG.KS.Pres

@[expose] noncomputable def rF (i : Nat) : Bool :=
  Nat.beq (wordPK 1782 11 Gs GIs (CFSG.KBRoute.Suz.rels.getD i [])) (pidn 1782 11)

#kc_each_unfold rF 0 30 as CertificateChecks.KernelSpor.Suz2306.r

end CertificateChecks.KernelSpor.Suz2306

end
