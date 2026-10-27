module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CFSG.KD.SuzB

#kc_repo #kc_nat_items_gz CFSG.KD.SuzB
  "Certificates/Kernel/Sporadic/SuzBridge/data/Regs.items.gz" 54607 15959660293506387929
  R[10] P1_[17] P2_[17]

#kc_repo #kc_json_gz CFSG.KD.SuzB
  "Certificates/Kernel/Sporadic/SuzBridge/data/Regs.json.gz" 62062 8803857003790192310
  (L : Nat) (H : Nat) (CM : Nat) (RM : Nat) (ONE : Nat) (LV : Nat) (HV : Nat) (R11 : Nat)
  (St1 : Nat) (St2 : Nat)

@[expose] noncomputable def R10 : Nat := R1

@[expose] noncomputable def R12 : Nat := R3

@[expose] noncomputable def R13 : Nat := R4

@[expose] noncomputable def R14 : Nat := R5

@[expose] noncomputable def R15 : Nat := R6

@[expose] noncomputable def R16 : Nat := R7

@[expose] noncomputable def R17 : Nat := R8

@[expose] noncomputable def R18 : Nat := R9

@[expose] noncomputable def R3bad : Nat := Nat.add R3 1

end CFSG.KD.SuzB

#kc_select CFSG.KD.SuzB RB R 19

#kc_select CFSG.KD.SuzB P1 P1_ 17

#kc_select CFSG.KD.SuzB P2 P2_ 17

end
