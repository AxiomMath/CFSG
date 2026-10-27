module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxHeartbeats 0
set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3884

#kc_repo #kc_json_gz CertificateChecks.KernelO8.SB3884
  "Certificates/Kernel/OmegaEight/data/SB3884S6.json.gz" 491515 13446387152279396459
  (cent6_0 : Nat × List Nat × Nat × Nat) (cent6_1 : Nat × List Nat × Nat × Nat)
  (cent6_2 : Nat × List Nat × Nat × Nat) (cent6_3 : Nat × List Nat × Nat × Nat)
  (cent6_4 : Nat × List Nat × Nat × Nat) (cent6_5 : Nat × List Nat × Nat × Nat)
  (recs6 : List (Nat × List Nat))

@[expose] noncomputable def cents6 : List (Nat × List Nat × Nat × Nat) :=
  [cent6_0, cent6_1, cent6_2, cent6_3, cent6_4, cent6_5]

end CertificateChecks.KernelO8.SB3884

end
