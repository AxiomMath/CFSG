module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxHeartbeats 0
set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3884

#kc_repo #kc_json_gz CertificateChecks.KernelO8.SB3884
  "Certificates/Kernel/OmegaEight/data/SB3884S0.json.gz" 491286 11008534024137497138
  (cent0_0 : Nat × List Nat × Nat × Nat) (cent0_1 : Nat × List Nat × Nat × Nat)
  (cent0_2 : Nat × List Nat × Nat × Nat) (cent0_3 : Nat × List Nat × Nat × Nat)
  (cent0_4 : Nat × List Nat × Nat × Nat) (cent0_5 : Nat × List Nat × Nat × Nat)
  (recs0 : List (Nat × List Nat))

@[expose] noncomputable def cents0 : List (Nat × List Nat × Nat × Nat) :=
  [cent0_0, cent0_1, cent0_2, cent0_3, cent0_4, cent0_5]

end CertificateChecks.KernelO8.SB3884

end
