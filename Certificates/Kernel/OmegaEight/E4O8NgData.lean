module

public import Certificates.Data.Kernel.PCent
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CertificateChecks.KernelO8.E4C

#kc_repo #kc_json_gz CertificateChecks.KernelO8.E4C
  "Certificates/Kernel/OmegaEight/data/E4O8NgData.json.gz" 549073 6541436923670890796
  (Y1 : Nat) (Y2 : Nat) (RY1 : List (Nat × Nat × Nat × Nat))
  (G4 : List Nat) (W4 : List (List Nat))
  (L4 : List (Nat × List Nat × List (List Nat) × List (Nat × Nat × Nat × Nat)))
  (RY2 : List (Nat × Nat × Nat × Nat))

@[expose] noncomputable def g4K (k : Nat) : Nat := G4.getD k (nat_lit 0)

@[expose] noncomputable def gi4K (k : Nat) : Nat := g4K (Nat.mod (Nat.add k (nat_lit 3)) (nat_lit 6))

end CertificateChecks.KernelO8.E4C

end
