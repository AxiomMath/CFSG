module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxHeartbeats 0
set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3884

#kc_repo #kc_json_gz CertificateChecks.KernelO8.SB3884
  "Certificates/Kernel/OmegaEight/data/SB3884S7.json.gz" 491515 10953216367016680581
  (cent7_0 : Nat × List Nat × Nat × Nat) (cent7_1 : Nat × List Nat × Nat × Nat)
  (cent7_2 : Nat × List Nat × Nat × Nat) (cent7_3 : Nat × List Nat × Nat × Nat)
  (cent7_4 : Nat × List Nat × Nat × Nat) (cent7_5 : Nat × List Nat × Nat × Nat)
  (recs7 : List (Nat × List Nat))

@[expose] noncomputable def cents7 : List (Nat × List Nat × Nat × Nat) :=
  [cent7_0, cent7_1, cent7_2, cent7_3, cent7_4, cent7_5]

end CertificateChecks.KernelO8.SB3884

end
