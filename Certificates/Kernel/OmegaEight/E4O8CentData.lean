module

public import Certificates.Data.Kernel.PCent
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CertificateChecks.KernelO8.E4C

#kc_repo #kc_json_gz CertificateChecks.KernelO8.E4C
  "Certificates/Kernel/OmegaEight/data/E4O8CentData.json.gz" 1732191 17182613344777502051
  (RX : List (Nat × Nat × Nat × Nat))
  (G0 : List Nat) (L0 : List (Nat × List Nat × List (List Nat) × List (Nat × Nat × Nat × Nat)))
  (RU : List (Nat × Nat × Nat × Nat))
  (G1 : List Nat) (W1 : List (List Nat))
  (L1 : List (Nat × List Nat × List (List Nat) × List (Nat × Nat × Nat × Nat)))
  (RV : List (Nat × Nat × Nat × Nat))
  (G2 : List Nat) (W2 : List (List Nat))
  (L2 : List (Nat × List Nat × List (List Nat) × List (Nat × Nat × Nat × Nat)))
  (C : Nat) (WC : List Nat) (RC : List (Nat × Nat × Nat × Nat))
  (G3 : List Nat) (W3 : List (List Nat)) (R3 : List (Nat × Nat × Nat × Nat))

@[expose] noncomputable def g0K (k : Nat) : Nat := G0.getD k (nat_lit 0)

@[expose] noncomputable def gi0K (k : Nat) : Nat := g0K (Nat.mod (Nat.add k (nat_lit 3)) (nat_lit 6))

@[expose] noncomputable def g1K (k : Nat) : Nat := G1.getD k (nat_lit 0)

@[expose] noncomputable def gi1K (k : Nat) : Nat := g1K (Nat.mod (Nat.add k (nat_lit 3)) (nat_lit 6))

@[expose] noncomputable def g2K (k : Nat) : Nat := G2.getD k (nat_lit 0)

@[expose] noncomputable def gi2K (k : Nat) : Nat := g2K (Nat.mod (Nat.add k (nat_lit 3)) (nat_lit 6))

@[expose] noncomputable def g3K (k : Nat) : Nat := G3.getD k (nat_lit 0)
end CertificateChecks.KernelO8.E4C

end
