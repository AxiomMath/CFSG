module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.HarnessGz
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.JsonFamilyGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24G2e.Data
public import Certificates.Kernel.Sporadic.Fi24G2d.Data
public import Certificates.Data.Kernel.Spor.Fi24G2e

#kc_repo #kc_ktree_gz CFSG.KD.Fi24G2e OX "Certificates/Kernel/Sporadic/Fi24G2e/data/own.bin.gz" 152491 4 457473 6795662934133295787
#kc_repo #kc_json_family_gz CFSG.KD.Fi24G2e "Certificates/Kernel/Sporadic/Fi24G2e/data/own_lists.json.gz" 39306 7386850248505593530
  (CQ : List Nat)
#kc_repo #kc_json_gz CFSG.KD.Fi24G2e "Certificates/Kernel/Sporadic/Fi24G2e/data/own_lists.json.gz" 39306 7386850248505593530
  (OQ2 : List Nat) (OQ4 : List Nat) (OQ6 : List Nat) (CY : List Nat)
#kc_listDispatch CFSG.KD.Fi24G2e CQL CQ 696

public section

namespace CFSG.KD.Fi24G2e

@[expose] noncomputable def MQ2 : Nat := OX 0

@[expose] noncomputable def MQ4 : Nat := OX 1

@[expose] noncomputable def MQ6 : Nat := OX 2

@[expose] noncomputable def CYF (j : Nat) : Nat := CY.getD j (nat_lit 0)

end CFSG.KD.Fi24G2e

end
