module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxHeartbeats 0
set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3884

#kc_repo #kc_json_gz CertificateChecks.KernelO8.SB3884
  "Certificates/Kernel/OmegaEight/data/SB3884S4.json.gz" 491515 9102238255565219533
  (cent4_0 : Nat × List Nat × Nat × Nat) (cent4_1 : Nat × List Nat × Nat × Nat)
  (cent4_2 : Nat × List Nat × Nat × Nat) (cent4_3 : Nat × List Nat × Nat × Nat)
  (cent4_4 : Nat × List Nat × Nat × Nat) (cent4_5 : Nat × List Nat × Nat × Nat)
  (recs4 : List (Nat × List Nat))

@[expose] noncomputable def cents4 : List (Nat × List Nat × Nat × Nat) :=
  [cent4_0, cent4_1, cent4_2, cent4_3, cent4_4, cent4_5]

end CertificateChecks.KernelO8.SB3884

end
