module

public import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItems
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000

#kc_repo #kc_nat_items CFSG.KD.Fi23Dce3 "Certificates/Kernel/Fi23U3/data/cover.tabs.items" 184692 6195833733146005910
  LO[12] LB[12]

#kc_select CFSG.KD.Fi23Dce3 FO LO 12
#kc_select CFSG.KD.Fi23Dce3 FB LB 12

#kc_repo #kc_nat_items CFSG.KD.Fi23Dce3 "Certificates/Kernel/Fi23U3/data/cover.tu.items" 95904 1940145838253375518
  TUL[8748]

#kc_select CFSG.KD.Fi23Dce3 TU TUL 8748

#kc_repo #kc_json CFSG.KD.Fi23Dce3 "Certificates/Kernel/Fi23U3/data/cover.chains.json" 3376476 16095369440373894873
  (DS : List Nat) (CV : List (List Nat)) (CG : List (List Nat)) (CW : List (List (List Nat)))
  (CB : List (List (List Nat))) (CS : List (List (List Nat))) (CT : List (List (List Nat)))
  (CN : List Nat)
