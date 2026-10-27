module

public import Certificates.Data.Kernel.PCentExt
public import Certificates.Kernel.G24Th799103.InvData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelG24Th

#kc_repo #kc_json_gz CertificateChecks.KernelG24Th
  "Certificates/Kernel/G24Th799103/data/m.json.gz" 497195 10513801421044380325
  (Y0 : Nat) (TM : Nat) (Q0 : List (Nat × Nat × Nat × Nat)) (AG : List Nat)
  (ST : List (Nat × Nat × Nat × Nat))
  (NM : List (Nat × List Nat × List (List Nat) × List (Nat × Nat × Nat × Nat)))
  (DG : List Nat) (XO : Nat) (RO : List (Nat × Nat × Nat × Nat)) (WM : List (List Nat))

open CertificateChecks.KernelG24.Tri27206

@[expose] noncomputable def xyG (k : Nat) : Nat := [LC.S 0, LC.S 1].getD k (nat_lit 0)

@[expose] noncomputable def aG (k : Nat) : Nat := AG.getD k (nat_lit 0)

@[expose] noncomputable def mG (k : Nat) : Nat := TG.F (Nat.add 6 k)

@[expose] noncomputable def dG (k : Nat) : Nat := DG.getD k (nat_lit 0)

end CertificateChecks.KernelG24Th

end
