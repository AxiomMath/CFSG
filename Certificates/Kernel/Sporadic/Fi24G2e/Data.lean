module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.JsonFamilyGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24Br.Data
public import Certificates.Kernel.Sporadic.Fi24Ext.Data
public import Certificates.Kernel.Sporadic.Fi24Fix.Data

#kc_repo #kc_ktree_gz CFSG.KD.Fi24G2e BX "Certificates/Kernel/Sporadic/Fi24G2e/data/bridge.bin.gz" 152491 4 2897329 7411202433937721026
#kc_repo #kc_json_family_gz CFSG.KD.Fi24G2e "Certificates/Kernel/Sporadic/Fi24G2e/data/bridge.json.gz" 265 14555122570214326293
  (PC : List Nat)
#kc_repo #kc_json_gz CFSG.KD.Fi24G2e "Certificates/Kernel/Sporadic/Fi24G2e/data/bridge.json.gz" 265 14555122570214326293
  (PL : List Nat) (PV : List Nat)

public section

namespace CFSG.KD.Fi24G2e

@[expose] noncomputable def LG (g : Nat) : Nat := BX g

@[expose] noncomputable def PM : Nat := BX (nat_lit 12)

@[expose] noncomputable def TQ : Nat := BX (nat_lit 13)

end CFSG.KD.Fi24G2e

end
