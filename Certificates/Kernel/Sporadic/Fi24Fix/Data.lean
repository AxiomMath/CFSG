module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24Br.Data
public import Certificates.Data.Kernel.Spor.Fi24Fix

#kc_repo #kc_ktree_gz CFSG.KD.Fi24Fix MX "Certificates/Kernel/Sporadic/Fi24Fix/data/mats.bin.gz" 152491 4 609964 15731757062940866396
#kc_repo #kc_json_gz CFSG.KD.Fi24Fix "Certificates/Kernel/Sporadic/Fi24Fix/data/word.json.gz" 82
  16998776890645267019 (W : List Nat)
#kc_repo #kc_ktree_gz CFSG.KD.Fi24Fix ST "Certificates/Kernel/Sporadic/Fi24Fix/data/orbit.bin.gz" 768 4 95013 197314662179044685

public section

namespace CFSG.KD.Fi24Fix

@[expose] noncomputable def R : Nat := MX 0

@[expose] noncomputable def Y : Nat := MX 1

@[expose] noncomputable def Q : Nat := MX 2

@[expose] noncomputable def C : Nat := MX 3

@[expose] noncomputable def S (j : Nat) : Nat :=
  fld(ST (Nat.shiftRight j (nat_lit 8)), Nat.mul (Nat.land j (nat_lit 255)) (nat_lit 24),
    nat_lit 16777215)

end CFSG.KD.Fi24Fix

end
