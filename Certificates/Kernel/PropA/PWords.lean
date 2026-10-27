module

public import Certificates.Kernel.PropA.Words

public section

namespace CertificateChecks.KernelPropA

@[expose] def pa450010wCKG : List (List Int) := pa450010wCDG ++ [[3], [4]]

@[expose] def pa450010wd : List Int :=
  [2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2]

end CertificateChecks.KernelPropA

end
