module

import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.JsonGz
public import Certificates.Data.Kernel.Wit3K
meta import Certificates.Kernel.Misc.PackJson
import Certificates.Kernel.Misc.PackJson

public section

#kc_repo #kmisc_json_pack CertificateChecks.KernelRonanWit.Tits
  "Certificates/Kernel/RonanWit/data/tits.json.gz" 246219 9329301388614281238
  (gens GS 11) (pG PG 11) (ppts PT 11) (pedges EP 12) (ppar PAR 0) (plab LAB 0) (pK K 0)
  (pso SO 0) (psi SI 0) (ys YS 11) (wit W 0)

#kc_repo #kc_json_gz CertificateChecks.KernelRonanWit.Tits
  "Certificates/Kernel/RonanWit/data/tits.json.gz" 246219 9329301388614281238
  (pws : List (List Nat)) (pps : List Nat) (yws : List (List Nat))

namespace CertificateChecks.KernelRonanWit.Tits

@[expose] noncomputable def P : CFSG.KC.Wit3.Cert := ⟨2, PG, pws, 27, PT, EP, PAR, LAB, pps, K, SO, SI⟩

end CertificateChecks.KernelRonanWit.Tits

end
