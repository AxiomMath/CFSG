module

import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.JsonGz
public import Certificates.Data.Kernel.Wit3K
meta import Certificates.Kernel.Misc.PackJson
import Certificates.Kernel.Misc.PackJson

public section

#kc_repo #kmisc_json_pack CertificateChecks.KernelRonanWit.D4
  "Certificates/Kernel/RonanWit/data/d4.json.gz" 986474 16129164334832019483
  (gens GS 12) (pG PG 12) (ppts PT 12) (pedges EP 12) (ppar PAR 0) (plab LAB 0) (pK K 0)
  (pso SO 0) (psi SI 0) (ys YS 12) (wit W 0)

#kc_repo #kc_json_gz CertificateChecks.KernelRonanWit.D4
  "Certificates/Kernel/RonanWit/data/d4.json.gz" 986474 16129164334832019483
  (pws : List (List Nat)) (pps : List Nat) (yws : List (List Nat))

namespace CertificateChecks.KernelRonanWit.D4

@[expose] noncomputable def P : CFSG.KC.Wit3.Cert := ⟨4, PG, pws, 81, PT, EP, PAR, LAB, pps, K, SO, SI⟩

end CertificateChecks.KernelRonanWit.D4

end
