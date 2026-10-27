module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxHeartbeats 0
set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3884

#kc_repo #kc_json_gz CertificateChecks.KernelO8.SB3884
  "Certificates/Kernel/OmegaEight/data/SB3884S1.json.gz" 491286 17017818381579473755
  (cent1_0 : Nat × List Nat × Nat × Nat) (cent1_1 : Nat × List Nat × Nat × Nat)
  (cent1_2 : Nat × List Nat × Nat × Nat) (cent1_3 : Nat × List Nat × Nat × Nat)
  (cent1_4 : Nat × List Nat × Nat × Nat) (cent1_5 : Nat × List Nat × Nat × Nat)
  (recs1 : List (Nat × List Nat))

@[expose] noncomputable def cents1 : List (Nat × List Nat × Nat × Nat) :=
  [cent1_0, cent1_1, cent1_2, cent1_3, cent1_4, cent1_5]

end CertificateChecks.KernelO8.SB3884

end
