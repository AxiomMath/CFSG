module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxHeartbeats 0
set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3884

#kc_repo #kc_json_gz CertificateChecks.KernelO8.SB3884
  "Certificates/Kernel/OmegaEight/data/SB3884S2.json.gz" 491286 4686856020485367426
  (cent2_0 : Nat × List Nat × Nat × Nat) (cent2_1 : Nat × List Nat × Nat × Nat)
  (cent2_2 : Nat × List Nat × Nat × Nat) (cent2_3 : Nat × List Nat × Nat × Nat)
  (cent2_4 : Nat × List Nat × Nat × Nat) (cent2_5 : Nat × List Nat × Nat × Nat)
  (recs2 : List (Nat × List Nat))

@[expose] noncomputable def cents2 : List (Nat × List Nat × Nat × Nat) :=
  [cent2_0, cent2_1, cent2_2, cent2_3, cent2_4, cent2_5]

end CertificateChecks.KernelO8.SB3884

end
