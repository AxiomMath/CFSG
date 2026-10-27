module

public import Certificates.Data.Kernel.HNLocalK
public import Certificates.Data.Kernel.HNLocal.W
public import Certificates.Data.Kernel.HNMultK
public import Certificates.Data.CFSGNative.HN.Local.AltData
public import Certificates.Data.CFSGNative.HN.Local.TypeData
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonFamilyGz
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.HNLocal "Certificates/Kernel/HNLocal/data/regs.items.gz" 3707301 17900193135692568574
    (R 0 95) (P 0 14) GA GB (GX 2 4) GT2 GT4 PF2 QF2 PF4 QF4 LC GFC MS (MSF 0 8) CM3 M TGN
#kc_repo #kc_json_family_gz CFSG.KD.HNLocal "Certificates/Kernel/HNLocal/data/regs.json.gz" 2650 6107227363552920052
  (WD : List Nat)
#kc_select CFSG.KD.HNLocal RB R 95
#kc_select CFSG.KD.HNLocal PC P 14
#kc_select CFSG.KD.HNLocal MSF MSF 8
#kc_listDispatch CFSG.KD.HNLocal WDL WD 45

public section

namespace CFSG.KD.HNLocal

noncomputable abbrev mul : Nat → Nat → Nat :=
  CFSG.KC.Ord.mulR 5 13 1729 133 9 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CFSG.KD.OrdHN.CM CFSG.KD.OrdHN.RM

noncomputable abbrev vm : Nat → Nat → Nat :=
  CFSG.KC.Ord.vecR 5 13 1729 133 9 CFSG.KD.OrdHN.LV CFSG.KD.OrdHN.HV CFSG.KD.OrdHN.RM

noncomputable abbrev vld : Nat → Bool := CFSG.KC.Ord.validM 5 229957 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H

@[expose] noncomputable def RP (a : Nat) : Nat := RB (Nat.add (nat_lit 16) a)

@[expose] noncomputable def TG (e : Nat) : Nat :=
  Nat.land (Nat.shiftRight TGN (Nat.mul (nat_lit 16) e)) (nat_lit 65535)

@[expose] noncomputable def PI2 (k : Nat) : Nat := CFSG.Sporadic.HN.Local.Native.altPi2[k]!

@[expose] noncomputable def PI3 (k : Nat) : Nat := CFSG.Sporadic.HN.Local.Native.altPi3[k]!

@[expose] noncomputable def PT2 (k : Nat) : Nat := CFSG.Sporadic.HN.Local.Native.typePi2[k]!

@[expose] noncomputable def PT4 (k : Nat) : Nat := CFSG.Sporadic.HN.Local.Native.typePi4[k]!

end CFSG.KD.HNLocal

end
