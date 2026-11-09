module

public import Certificates.Kernel.Misc.Perm.HS100.Base

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.Clique

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CertificateChecks.KernelMisc.HS100

@[expose] noncomputable def X3 : Nat :=
  pcomp 100 7 (mask 7) (pcomp 100 7 (mask 7) (HX.F 0) (HX.F 15))
    (pcomp 100 7 (mask 7) (HX.F 0) (HX.F 15))

end CertificateChecks.KernelMisc.HS100.Clique

end
