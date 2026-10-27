module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.JsonFamilyGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24G2e.Data

#kc_repo #kc_ktree_gz CFSG.KD.Fi24G2e RX "Certificates/Kernel/Sporadic/Fi24G2e/data/reps.bin.gz" 152491 4 7929532 11901051539900107191
#kc_repo #kc_json_family_gz CFSG.KD.Fi24G2e "Certificates/Kernel/Sporadic/Fi24G2e/data/reps_lists.json.gz" 501 14838592602686944896
  (CW : List Nat) (GW : List Nat) (GC : List Nat) (HW : List Nat) (CH : List Nat) (NO : Nat)
#kc_repo #kc_json_gz CFSG.KD.Fi24G2e "Certificates/Kernel/Sporadic/Fi24G2e/data/reps_lists.json.gz" 501 14838592602686944896
  (WWL : List Nat) (WIL : List Nat)
#kc_listDispatch CFSG.KD.Fi24G2e CWL CW 7
#kc_listDispatch CFSG.KD.Fi24G2e GWL GW 7
#kc_listDispatch CFSG.KD.Fi24G2e GCL GC 7
#kc_listDispatch CFSG.KD.Fi24G2e CHL CH 7

public section

namespace CFSG.KD.Fi24G2e

@[expose] noncomputable def HS : Nat := RX 0

@[expose] noncomputable def D1H : Nat := RX 1

@[expose] noncomputable def D1 : Nat := RX 2

@[expose] noncomputable def D2 : Nat := RX 3

@[expose] noncomputable def D4 : Nat := RX 4

@[expose] noncomputable def D6 : Nat := RX 5

@[expose] noncomputable def RD : Nat := RX 6

@[expose] noncomputable def RU2 : Nat := RX 7

@[expose] noncomputable def WW : Nat := RX 8

@[expose] noncomputable def WI : Nat := RX 9

@[expose] noncomputable def RU3 : Nat := RX 10

@[expose] noncomputable def RDT : Nat := RX 11

@[expose] noncomputable def RU2T : Nat := RX 12

@[expose] noncomputable def RU3T : Nat := RX 13

@[expose] noncomputable def MWA : Nat := RX 14

@[expose] noncomputable def MWD : Nat := RX 15

@[expose] noncomputable def MWB : Nat := RX 16

@[expose] def YB : List Nat := [17, 21, 25, 32, 35, 38, 44]

@[expose] noncomputable def YY (i : Nat) : Nat := RX (YB.getD i 0)

@[expose] noncomputable def ZZ (i : Nat) : Nat := RX (Nat.succ (YB.getD i 0))

@[expose] noncomputable def REP (i : Nat) : Nat :=
  [RD, RU2, RU3, CFSG.KD.Fi24Ext.T, RDT, RU2T, RU3T].getD i 0

@[expose] noncomputable def HR (z : Nat) : Nat :=
  nIf(Nat.beq z (nat_lit 1), CFSG.KD.Fi24Ext.H0, nIf(Nat.beq z (nat_lit 2), CFSG.KD.Fi24Ext.H1, HS))

@[expose] def nO (i : Nat) : Nat := [5, 5, 27, 3, 3, 11, 33].getD i 1

end CFSG.KD.Fi24G2e

end
