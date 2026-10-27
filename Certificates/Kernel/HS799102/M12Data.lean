module

public import Certificates.Kernel.HS799102.GlueData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS799102

#kc_repo #kc_json_gz CertificateChecks.KernelHS799102
  "Certificates/Kernel/HS799102/data/m12.json.gz" 4666 5018747758190876224
  (G12 : List Nat) (A12 : List Nat) (X12 : Nat) (O12 : List (Nat × Nat × Nat × Nat))
  (N12 : List (Nat × List Nat × List (List Nat) × List (Nat × Nat × Nat × Nat)))
  (W12 : List (List Nat)) (Y12 : Nat)

@[expose] noncomputable def mG12 (k : Nat) : Nat := G12.getD k (nat_lit 0)

@[expose] noncomputable def aW12 (k : Nat) : Nat := A12.getD k (nat_lit 0)

@[expose] noncomputable def dG12 (k : Nat) : Nat := dGen aW12 (nat_lit 0) k

end CertificateChecks.KernelHS799102

end
