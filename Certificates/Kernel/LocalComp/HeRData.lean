module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CertificateChecks.KernelLC.HeR
  "Certificates/Kernel/LocalComp/data/her.json.gz" 280913 16974495370045063118
  (HRI0 : Nat) (HRI1 : Nat) (HRI2 : Nat) (HRI3 : Nat) (HRI4 : Nat) (HRI5 : Nat) (HRI6 : Nat)
  (HRI7 : Nat)

public section

namespace CertificateChecks.KernelLC.HeR

@[expose] noncomputable def HRI (i : Nat) : Nat :=
  [HRI0, HRI1, HRI2, HRI3, HRI4, HRI5, HRI6, HRI7].getD i 0

end CertificateChecks.KernelLC.HeR

end
