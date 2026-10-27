module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxHeartbeats 0
set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3884

#kc_repo #kc_json_gz CertificateChecks.KernelO8.SB3884
  "Certificates/Kernel/OmegaEight/data/SB3884S5.json.gz" 491515 9459723647789878360
  (cent5_0 : Nat × List Nat × Nat × Nat) (cent5_1 : Nat × List Nat × Nat × Nat)
  (cent5_2 : Nat × List Nat × Nat × Nat) (cent5_3 : Nat × List Nat × Nat × Nat)
  (cent5_4 : Nat × List Nat × Nat × Nat) (cent5_5 : Nat × List Nat × Nat × Nat)
  (recs5 : List (Nat × List Nat))

@[expose] noncomputable def cents5 : List (Nat × List Nat × Nat × Nat) :=
  [cent5_0, cent5_1, cent5_2, cent5_3, cent5_4, cent5_5]

end CertificateChecks.KernelO8.SB3884

end
