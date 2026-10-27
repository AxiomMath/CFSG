module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxHeartbeats 0
set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3884

#kc_repo #kc_json_gz CertificateChecks.KernelO8.SB3884
  "Certificates/Kernel/OmegaEight/data/SB3884S3.json.gz" 491286 14357398128942285471
  (cent3_0 : Nat × List Nat × Nat × Nat) (cent3_1 : Nat × List Nat × Nat × Nat)
  (cent3_2 : Nat × List Nat × Nat × Nat) (cent3_3 : Nat × List Nat × Nat × Nat)
  (cent3_4 : Nat × List Nat × Nat × Nat) (cent3_5 : Nat × List Nat × Nat × Nat)
  (recs3 : List (Nat × List Nat))

@[expose] noncomputable def cents3 : List (Nat × List Nat × Nat × Nat) :=
  [cent3_0, cent3_1, cent3_2, cent3_3, cent3_4, cent3_5]

end CertificateChecks.KernelO8.SB3884

end
