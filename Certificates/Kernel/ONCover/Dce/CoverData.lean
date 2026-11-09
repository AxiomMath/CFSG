module

public import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItems
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000

#kc_repo #kc_nat_items CFSG.KD.ONCoverDce3 "Certificates/Kernel/ONCover/data/mainWs.tabs.items" 235644 6682345310772939160
  LO[12] LB[12]

#kc_select CFSG.KD.ONCoverDce3 FO LO 12
#kc_select CFSG.KD.ONCoverDce3 FB LB 12

#kc_repo #kc_json CFSG.KD.ONCoverDce3 "Certificates/Kernel/ONCover/data/mainWs.cover.json" 1920250 12116859078647805410
  (DS : List Nat) (CV : List (List Nat)) (CG : List (List Nat)) (CW : List (List (List Nat)))
  (CB : List (List (List Nat))) (CS : List (List (List Nat))) (CT : List (List (List Nat)))
  (CN : List Nat)
