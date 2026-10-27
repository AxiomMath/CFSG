module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.JsonFamilyGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24G2d.Data
public import Certificates.Data.Kernel.Spor.Fi24G2e

#kc_repo #kc_json_family_gz CFSG.KD.Fi24G2e "Certificates/Kernel/Sporadic/Fi24G2e/data/leaves.json.gz" 716 6379849587105100716
  (LW0_ : List Nat) (LE0_ : Nat) (LO0_ : Nat) (OWN : List Nat) (OWV : List Nat) (LW1_ : List Nat)
  (LE1_ : Nat) (LO1_ : Nat)
#kc_repo #kc_json_gz CFSG.KD.Fi24G2e "Certificates/Kernel/Sporadic/Fi24G2e/data/leaves.json.gz" 716 6379849587105100716
  (NODE : List Nat)
#kc_repo #kc_ktree_gz CFSG.KD.Fi24G2e LTB "Certificates/Kernel/Sporadic/Fi24G2e/data/ltab.bin.gz" 1280 4 107520 8031026484664664322
#kc_listDispatch CFSG.KD.Fi24G2e LWL0 LW0_ 6
#kc_listDispatch CFSG.KD.Fi24G2e LWL1 LW1_ 6
#kc_select CFSG.KD.Fi24G2e LEN0 LE0_ 6
#kc_select CFSG.KD.Fi24G2e LEN1 LE1_ 6
#kc_select CFSG.KD.Fi24G2e LON0 LO0_ 6
#kc_select CFSG.KD.Fi24G2e LON1 LO1_ 6

public section

namespace CFSG.KD.Fi24G2e

@[expose] noncomputable def FLC0 : Nat → Nat := CFSG.KD.Fi24G2d.F2B

@[expose] noncomputable def FLC1 : Nat → Nat := CFSG.KD.Fi24G2d.F2D

@[expose] def LWC0 : List Nat := CFSG.KD.Fi24G2d.W2B

@[expose] def LWC1 : List Nat := CFSG.KD.Fi24G2d.W2D

@[expose] noncomputable def TB0 (k i : Nat) : Nat := fld(LTB k, Nat.mul i (nat_lit 10), nat_lit 1023)

@[expose] noncomputable def TI0 (k i : Nat) : Nat :=
  fld(LTB (Nat.add (nat_lit 21) k), Nat.mul i (nat_lit 10), nat_lit 1023)

@[expose] noncomputable def TB1 (k i : Nat) : Nat :=
  fld(LTB (Nat.add (nat_lit 42) k), Nat.mul i (nat_lit 10), nat_lit 1023)

@[expose] noncomputable def TI1 (k i : Nat) : Nat :=
  fld(LTB (Nat.add (nat_lit 63) k), Nat.mul i (nat_lit 10), nat_lit 1023)

end CFSG.KD.Fi24G2e

end
