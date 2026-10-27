module

import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CertificateChecks.KernelO8.Q125

#kc_repo #kc_ktree_gz CertificateChecks.KernelO8.Q125 MT
  "Certificates/Kernel/OmegaEight/data/q125m.bin.gz" 30 4 189000 552396053132579240
#kc_repo #kc_ktree_gz CertificateChecks.KernelO8.Q125 RT
  "Certificates/Kernel/OmegaEight/data/q125r.bin.gz" 16 4 100800 16974492948908910445
#kc_repo #kc_json_gz CertificateChecks.KernelO8.Q125
  "Certificates/Kernel/OmegaEight/data/q125.json.gz" 32271 16307487912887749620
  (roots : List (Nat × Nat × Nat × Nat × List (Nat × Nat))) (wit37 : Nat) (wit37i : Nat)
  (lists : List (List Nat)) (g0perm : List (List Nat)) (swaps : List (List (Nat × Nat)))

end CertificateChecks.KernelO8.Q125

end
