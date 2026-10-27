module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Fam.HNSeed.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonFamilyGz
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CFSG.KD.HNMult

noncomputable abbrev mul : Nat → Nat → Nat :=
  CFSG.KC.Ord.mulR 5 13 1729 133 9 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H CFSG.KD.FamHNSeed.CM
    CFSG.KD.FamHNSeed.RM

noncomputable abbrev vld : Nat → Bool :=
  CFSG.KC.Ord.validM 5 229957 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H

end CFSG.KD.HNMult

#kc_repo #kc_nat_items_gz CFSG.KD.HNMult "Certificates/Kernel/HNMult/data/regs.items.gz" 747329 4529208474318486799
    (R 0 27)
#kc_repo #kc_json_family_gz CFSG.KD.HNMult "Certificates/Kernel/HNMult/data/regs.json.gz" 8800 7238507709139029673
  (W : List Nat)
#kc_select CFSG.KD.HNMult RB R 27
#kc_listDispatch CFSG.KD.HNMult WD W 86

end
