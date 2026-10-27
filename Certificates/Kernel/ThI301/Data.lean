module

public import Init
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CFSG.KD.ThI301 "Certificates/Kernel/ThI301/data/gens.json.gz" 205
  6794993328121371484 (A : Nat) (AI : Nat) (B : Nat) (BI : Nat) (Y : List Nat) (YI : List Nat)
  (PM : Nat) (RO : Nat) (NL : Nat)

#kc_repo #kc_ktree_gz CFSG.KD.ThI301 IT "Certificates/Kernel/ThI301/data/invol.bin.gz" 9 4
  23571 8943540531612570244

public section

namespace CFSG.KD.ThI301

@[expose] noncomputable def yP (k : Nat) : Nat := List.getD Y k (nat_lit 0)

@[expose] noncomputable def yPI (k : Nat) : Nat := List.getD YI k (nat_lit 0)

end CFSG.KD.ThI301

end
