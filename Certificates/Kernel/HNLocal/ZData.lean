module

public import Certificates.Data.Kernel.HNLocalZ
public import Certificates.Kernel.HNLocal.Data
public import Certificates.Data.Kernel.HNMultK
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonFamilyGz
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.HNLocalZ "Certificates/Kernel/HNLocal/data/zregs.items.gz" 4977154 13728104516755301160
    TZ EV EZ (R 0 173)
#kc_repo #kc_json_family_gz CFSG.KD.HNLocalZ "Certificates/Kernel/HNLocal/data/zregs.json.gz" 6244 4849985139563199706
  (WZ : List Nat)
#kc_select CFSG.KD.HNLocalZ RZ R 173
#kc_listDispatch CFSG.KD.HNLocalZ WZL WZ 127

public section

namespace CFSG.KD.HNLocalZ

@[expose] noncomputable def TZT (e : Nat) : Nat :=
  Nat.land (Nat.shiftRight TZ (Nat.mul (nat_lit 16) e)) (nat_lit 65535)

@[expose] noncomputable def zChunk (m : Nat) : Bool :=
  CFSG.KC.HNLocal.zcenAt CFSG.KD.HNLocal.mul CFSG.KD.HNLocal.vm CFSG.KD.HNLocal.PC TZT
    CFSG.KD.OrdHN.ONE CFSG.KD.OrdHN.RM EZ EV m (nat_lit 4) (nat_lit 10)

@[expose] noncomputable def zRel (c : Nat) : Bool :=
  CFSG.KC.HNMult.relWRange RZ CFSG.KD.HNLocal.mul (nat_lit 86) CFSG.KD.OrdHN.ONE WZL
    (Nat.mul (nat_lit 16) c) (Nat.min (nat_lit 16) (Nat.sub (nat_lit 127) (Nat.mul (nat_lit 16) c)))

end CFSG.KD.HNLocalZ

end
